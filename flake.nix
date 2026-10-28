{
  description = "jihoo: a systems language as fast as C, memory-safe without lifetimes";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      lib = nixpkgs.lib;
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      version = "0.1.3";

      # Only what the compiler needs, so that editing the website (or docs)
      # does not rebuild it.
      src = lib.fileset.toSource {
        root = ./.;
        fileset = lib.fileset.unions [
          ./compiler
          ./lib
          ./examples
          ./tests
        ];
      };

      # The seed: the compiler of a release (see .github/workflows/release.yml),
      # which builds this one. compiler/ and the lib/ it imports may use only
      # what the seed knows; to use something new there, release the compiler
      # that has it and move the seed here.
      seed = {
        version = "0.1.3";
        hash = {
          x86_64-linux = "sha256-MpL62gAJMk3PRrLYfjxj3Ut99hkU624fufH0XMCi6YU=";
          aarch64-linux = "sha256-0bWJJvAcJu9EmNYJpA2x4Xp6KdWVIyCnHqK/KkTLmqs=";
        };
      };

      meta = {
        homepage = "https://jihoolang.github.io/jihoo/";
        license = lib.licenses.asl20;
        platforms = lib.platforms.linux;
      };

      # LLVM's C API optimizes IR and emits objects in process. Keep the
      # shared library at major version 21, as checked by both backends.
      llvmFor = pkgs: pkgs.llvmPackages_21;

      # Ship the standard library, libLLVM, and native/freestanding linkers.
      wrapCompiler = llvm: ''
        mkdir -p $out/share/jihoo
        cp -r lib $out/share/jihoo/lib
        wrapProgram $out/bin/jihoo \
          --suffix JIHOO_PATH : $out/share/jihoo/lib \
          --set-default JIHOO_CC ${llvm.clang}/bin/clang \
          --set-default JIHOO_LLVM ${llvm.llvm.lib}/lib/libLLVM-21.so \
          --set-default JIHOO_LD ${llvm.lld}/bin/ld.lld \
          --prefix PATH : ${llvm.lld}/bin
      '';

      mkPackages = pkgs:
        let llvm = llvmFor pkgs; in
        rec {
          # Stage 0: the released compiler, its loader and libgcc_s
          # patched in for Nix.
          jihoo-seed = pkgs.stdenv.mkDerivation {
            pname = "jihoo-seed";
            inherit (seed) version;
            src = pkgs.fetchurl {
              url = "https://github.com/jihoolang/jihoo/releases/download/v${seed.version}/jihoo-v${seed.version}-${pkgs.stdenv.hostPlatform.parsed.cpu.name}-linux.tar.gz";
              hash = seed.hash.${pkgs.stdenv.hostPlatform.system};
            };
            nativeBuildInputs = [ pkgs.autoPatchelfHook pkgs.makeWrapper ];
            buildInputs = [ pkgs.stdenv.cc.cc.lib ];
            installPhase = ''
              mkdir -p $out
              cp -r bin share $out/
              wrapProgram $out/bin/jihoo \
                --set-default JIHOO_CC ${llvm.clang}/bin/clang \
                --set-default JIHOO_LLVM ${llvm.llvm.lib}/lib/libLLVM-21.so \
                --set-default JIHOO_LD ${llvm.lld}/bin/ld.lld
            '';
            meta = meta // {
              description = "The released jihoo compiler that bootstraps this one";
              mainProgram = "jihoo";
            };
          };

          # The compiler (compiler/): the seed builds it (stage 1),
          # stage 1 builds it again (stage 2), and stage 2 is installed
          # once stages 1 and 2 write the same IR for it: a fixed point.
          jihoo = pkgs.stdenv.mkDerivation {
            pname = "jihoo";
            inherit version src;
            nativeBuildInputs = [ jihoo-seed pkgs.makeWrapper ];
            buildPhase = ''
              runHook preBuild
              export JIHOO_PATH=$PWD/lib JIHOO_CC=${llvm.clang}/bin/clang
              export JIHOO_LLVM=${llvm.llvm.lib}/lib/libLLVM-21.so
              export JIHOO_LD=${llvm.lld}/bin/ld.lld
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
      # passes the tests of tests/runner.jh.
      checks = forAllSystems (pkgs:
        let
          llvm = llvmFor pkgs;
          jihoo = self.packages.${pkgs.stdenv.hostPlatform.system}.jihoo;
          otherTarget = if pkgs.stdenv.hostPlatform.isx86_64 then "aarch64" else "x86_64";
        in
        {
          # tests/runner.jh, built and run by the installed compiler, tests
          # it: the programs of tests/run, tests/fail and examples, the
          # backend, and that it builds a compiler that writes the same IR.
          tests = pkgs.stdenv.mkDerivation {
            pname = "jihoo-tests";
            inherit version src;
            nativeBuildInputs = [ jihoo llvm.clang llvm.lld pkgs.python3 ];
            dontConfigure = true;
            buildPhase = ''
              export JIHOO_PATH=$PWD/lib JIHOO_COMPILER=${jihoo}/bin/jihoo
              jihoo run tests/runner.jh
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
              # `jihoo`: the seed, which builds compiler/
              self.packages.${pkgs.stdenv.hostPlatform.system}.jihoo-seed
              llvm.clang # native linker driver; C source link inputs
              llvm.lld # links freestanding programs
              llvm.llvm # opt, llc, llvm-dis for looking at what the compiler writes
              pkgs.python3 # independent JSON diagnostic validation and benchmark scripts
            ];
            JIHOO_LLVM = "${llvm.llvm.lib}/lib/libLLVM-21.so";
            JIHOO_LD = "${llvm.lld}/bin/ld.lld";
            # The checkout's standard library, not the seed's.
            shellHook = ''
              export JIHOO_PATH=$PWD/lib
            '';
          };

          # For working on the website in site/.
          site = pkgs.mkShell { packages = [ pkgs.nodejs ]; };
        });
    };
}
