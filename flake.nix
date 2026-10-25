{
  description = "jihoo: a systems language as fast as C, memory-safe without lifetimes";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      lib = nixpkgs.lib;
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      version = "0.1.0";

      # Only what the compiler needs, so that editing the website (or docs)
      # does not rebuild it.
      src = lib.fileset.toSource {
        root = ./.;
        fileset = lib.fileset.unions [
          ./Cargo.toml
          ./Cargo.lock
          ./crates
          ./compiler
          ./lib
          ./examples
          ./tests
        ];
      };

      meta = {
        homepage = "https://jihoolang.github.io/jihoo/";
        license = lib.licenses.asl20;
        platforms = lib.platforms.linux;
      };

      # Change the LLVM version here only. The compiler writes LLVM IR as
      # text, which this clang compiles and links.
      llvmFor = pkgs: pkgs.llvmPackages_21;

      # Ship the standard library, and clang and lld to finish programs.
      wrapCompiler = llvm: ''
        mkdir -p $out/share/jihoo
        cp -r lib $out/share/jihoo/lib
        wrapProgram $out/bin/jihoo \
          --suffix JIHOO_PATH : $out/share/jihoo/lib \
          --set-default JIHOO_CC ${llvm.clang}/bin/clang \
          --prefix PATH : ${llvm.lld}/bin
      '';

      mkPackages = pkgs:
        let llvm = llvmFor pkgs; in
        rec {
          # Stage 0: the compiler in Rust (crates/jihoo), which only
          # bootstraps the compiler in jihoo.
          jihoo-bootstrap = pkgs.rustPlatform.buildRustPackage {
            pname = "jihoo-bootstrap";
            inherit version src;
            cargoLock.lockFile = ./Cargo.lock;
            nativeBuildInputs = [ pkgs.makeWrapper ];

            # The tests compile and run programs, native and freestanding,
            # and build the compiler in jihoo to compare it with this one.
            nativeCheckInputs = [ llvm.clang llvm.lld ];
            preCheck = ''
              export JIHOO_CC=${llvm.clang}/bin/clang
            '';

            postInstall = wrapCompiler llvm;
            meta = meta // {
              description = "The jihoo compiler written in Rust, to bootstrap the one written in jihoo";
              mainProgram = "jihoo";
            };
          };

          # The compiler in jihoo (compiler/): stage 0 builds it (stage 1),
          # stage 1 builds it again (stage 2), and stage 2 is installed
          # once stages 1 and 2 write the same IR for it: a fixed point.
          jihoo = pkgs.stdenv.mkDerivation {
            pname = "jihoo";
            inherit version src;
            nativeBuildInputs = [ jihoo-bootstrap pkgs.makeWrapper ];
            buildPhase = ''
              runHook preBuild
              export JIHOO_PATH=$PWD/lib JIHOO_CC=${llvm.clang}/bin/clang
              jihoo build -O2 compiler/main.jh -o stage1
              ./stage1 build -O2 compiler/main.jh -o stage2
              ./stage1 emit-llvm compiler/main.jh -o stage1.ll
              ./stage2 emit-llvm compiler/main.jh -o stage2.ll
              if ! cmp -s stage1.ll stage2.ll; then
                echo "stages 1 and 2 write different IR for compiler/main.jh" >&2
                exit 1
              fi
              runHook postBuild
            '';
            installPhase = ''
              runHook preInstall
              install -Dm755 stage2 $out/bin/jihoo
              ${wrapCompiler llvm}
              runHook postInstall
            '';
            meta = meta // {
              description = "The jihoo compiler and standard library";
              mainProgram = "jihoo";
            };
          };

          default = jihoo;
        };
    in
    {
      packages = forAllSystems mkPackages;

      overlays.default = final: prev: {
        inherit (mkPackages final) jihoo;
      };

      apps = forAllSystems (pkgs: {
        default = {
          type = "app";
          program = "${self.packages.${pkgs.stdenv.hostPlatform.system}.jihoo}/bin/jihoo";
          meta.description = "Run the jihoo compiler";
        };
      });

      # `nix flake check`: the installed compiler (stage 2), used from
      # outside the source tree, builds and runs the examples, natively and
      # freestanding, and cross-compiles one for the other machine; and it
      # passes the tests of tests/run and tests/fail. Building the packages
      # runs the Rust compiler's tests, which compare the two compilers.
      checks = forAllSystems (pkgs:
        let
          llvm = llvmFor pkgs;
          jihoo = self.packages.${pkgs.stdenv.hostPlatform.system}.jihoo;
          otherTarget = if pkgs.stdenv.hostPlatform.isx86_64 then "aarch64" else "x86_64";
        in
        {
          programs = pkgs.rustPlatform.buildRustPackage {
            pname = "jihoo-programs-check";
            inherit version src;
            cargoLock.lockFile = ./Cargo.lock;
            nativeCheckInputs = [ llvm.clang llvm.lld ];
            cargoTestFlags = [ "--test" "programs" ];
            preCheck = ''
              export JIHOO_COMPILER=${jihoo}/bin/jihoo
            '';
            installPhase = "touch $out";
          };

          toolchain = pkgs.runCommand "jihoo-toolchain-check" { nativeBuildInputs = [ jihoo ]; } ''
            cp ${./examples}/*.jh .
            jihoo run hello.jh > hello.out
            grep -qx "Hello, jihoo!" hello.out
            jihoo run calc.jh > calc.out
            grep -qx 42 calc.out
            jihoo build freestanding.jh -o freestanding
            ./freestanding > fs.out && status=0 || status=$?
            test "$status" = 0
            grep -qx 5050 fs.out
            jihoo build --target ${otherTarget} freestanding.jh -o freestanding-${otherTarget}
            touch $out
          '';
        });

      devShells = forAllSystems (pkgs:
        let llvm = llvmFor pkgs; in
        {
          default = pkgs.mkShell {
            nativeBuildInputs = [
              pkgs.cargo
              pkgs.rustc
              pkgs.rustfmt
              pkgs.clippy
              pkgs.rust-analyzer
              llvm.clang # finishes programs: LLVM IR to executables
              llvm.lld # links freestanding programs
              llvm.llvm # opt, llc, llvm-dis for looking at what the compiler writes
            ];
            RUST_SRC_PATH = "${pkgs.rustPlatform.rustLibSrc}";
          };

          # For working on the website in site/.
          site = pkgs.mkShell { packages = [ pkgs.nodejs ]; };
        });
    };
}
