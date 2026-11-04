{
  description = "jihoo: a systems language as fast as C, memory-safe without lifetimes";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # Horn's Agda development (agda/), which agda/Adequacy.agda builds on.
  inputs.horn = {
    url = "github:jihoo12/horn";
    flake = false;
  };

  outputs = { self, nixpkgs, horn }:
    let
      lib = nixpkgs.lib;
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      version = "0.4.7";

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
        version = "0.4.7";
        hash = {
          x86_64-linux = "sha256-5GSLxuj2xQHIGS9QoGWY8b7YSafereedwXmA1E1snA0=";
          aarch64-linux = "sha256-gMrukqvGzggbx9kM6qKdbCy1dZos5bcHYvKZDNd8ThI=";
        };
      };

      meta = {
        homepage = "https://jihoolang.github.io/jihoo/";
        license = lib.licenses.asl20;
        platforms = lib.platforms.linux;
      };

      # What the uefi suite of tests/runner.jh runs UEFI programs with: QEMU,
      # OVMF and the UEFI shell, for x86_64 programs on x86_64 machines.
      uefiTestEnv = pkgs: lib.optionalAttrs pkgs.stdenv.hostPlatform.isx86_64 {
        JIHOO_QEMU = "${pkgs.qemu_test}/bin/qemu-system-x86_64";
        JIHOO_OVMF = "${pkgs.OVMF.fd}/FV/OVMF.fd";
        JIHOO_UEFI_SHELL = "${pkgs.edk2-uefi-shell}/shell.efi";
      };

      # LLVM's C API optimizes IR and emits objects in process. Keep the
      # shared library at major version 21, as checked by both backends.
      llvmFor = pkgs: pkgs.llvmPackages_21;

      hornCheckerFor = pkgs: pkgs.rustPlatform.buildRustPackage {
        pname = "jihoo-horn-checker";
        version = "0.3.0";
        src = horn;
        cargoLock.lockFile = "${horn}/Cargo.lock";
      };

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
            # The compiler's VERSION (compiler/main.jh) must be this package's.
            doInstallCheck = true;
            installCheckPhase = ''
              runHook preInstallCheck
              [ "$($out/bin/jihoo --version)" = "jihoo ${version}" ] || {
                echo "jihoo --version does not report ${version}" >&2
                exit 1
              }
              runHook postInstallCheck
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
          hornChecker = hornCheckerFor pkgs;
        in
        {
          # A semantic specification for the VC generator and local
          # erasure, independent of the compiler and the Horn certificate.
          # Loops, opaque effects and retained failures are covered; bad
          # proposed conditions must be rejected by Agda's type checker.
          check-removal = pkgs.runCommand "jihoo-check-removal" {
            nativeBuildInputs = [ pkgs.agda ];
          } ''
            cp -R ${./agda} agda
            chmod -R u+w agda
            export HOME=$TMPDIR LC_ALL=C.UTF-8
            HORN=${horn} bash agda/check-removal.sh
            touch $out
          '';

          # Execution-to-model bridge for the checker's three list sorts,
          # against the current emit-horn output, with malformed-rule tests.
          list-execution = pkgs.runCommand "jihoo-list-execution" {
            nativeBuildInputs = [ jihoo pkgs.agda ];
          } ''
            cp -R ${src}/. src
            chmod -R u+w src
            cp -R ${./agda} src/agda
            cd src
            export JIHOO_PATH=$PWD/lib HOME=$TMPDIR LC_ALL=C.UTF-8
            HORN=${horn} bash agda/check-lists.sh
            touch $out
          '';

          # Retain the actual proof for independent consumers: the theory,
          # goals and certificate, checked again by Horn's Rust checker, and
          # their Agda export, which the `adequacy` check has Agda check.
          certificate = pkgs.runCommand "jihoo-soundness-certificate" {
            nativeBuildInputs = [ jihoo hornChecker ];
          } ''
            cp -R ${src}/. src
            chmod -R u+w src
            cp -R ${./agda} src/agda
            cd src
            export JIHOO_PATH=$PWD/lib
            mkdir -p "$out"
            jihoo emit-horn --lib compiler/linear.jh --fn check > "$out/check.horn"
            jihoo run agda/certificate.jh -- "$out/check.horn" "$out"
            schematic-kernel "$out/check.theory" "$out/check.goals" "$out/check.proof" > "$out/checked.txt"
            schematic-kernel --agda CheckCertificate "$out/check.theory" "$out/check.goals" "$out/check.proof" \
              "$out/CheckCertificate.agda" > /dev/null
            # Fail if a missing result or a result pointing at the wrong
            # fact is accepted. Keep the original proof intact.
            sed '/^(result /d' "$out/check.proof" > missing.proof
            sed 's/^(result check_sound [0-9]*)$/(result check_sound 0)/' "$out/check.proof" > wrong.proof
            for bad in missing wrong; do
              if schematic-kernel "$out/check.theory" "$out/check.goals" "$bad.proof" > "$bad.log" 2>&1; then
                echo "accepted corrupted certificate: $bad" >&2
                exit 1
              fi
              cp "$bad.log" "$out/$bad-rejected.txt"
            done
          '';

          # tests/runner.jh, built and run by the installed compiler, tests
          # it: the programs of tests/run, tests/fail and examples, the
          # backend, that it builds a compiler that writes the same IR, and
          # UEFI programs in QEMU.
          tests = pkgs.stdenv.mkDerivation ({
            pname = "jihoo-tests";
            inherit version src;
            nativeBuildInputs = [ jihoo llvm.clang llvm.lld pkgs.python3 ];
            dontConfigure = true;
            buildPhase = ''
              export JIHOO_PATH=$PWD/lib JIHOO_COMPILER=${jihoo}/bin/jihoo
              jihoo run tests/runner.jh
            '';
            installPhase = "touch $out";
          } // uefiTestEnv pkgs);

          # agda/check.sh: the certificate lib/proof/refine.jh produces that
          # the linear checker is sound, checked by Agda running Horn's
          # proved checker (agda/ImplicationCheck.agda), and the theorem read
          # in the integers.
          adequacy = pkgs.runCommand "jihoo-adequacy" { nativeBuildInputs = [ jihoo pkgs.agda hornChecker ]; } ''
            cp -R ${src}/. src
            chmod -R u+w src
            cp -R ${./agda} src/agda
            cd src
            # Agda's messages contain Unicode.
            export JIHOO_PATH=$PWD/lib HOME=$TMPDIR LC_ALL=C.UTF-8
            HORN=${horn} JIHOO=jihoo bash agda/check.sh
            touch $out
          '';

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
        let
          llvm = llvmFor pkgs;
          shell = {
            nativeBuildInputs = [
              # `jihoo`: the seed, which builds compiler/
              self.packages.${pkgs.stdenv.hostPlatform.system}.jihoo-seed
              llvm.clang # native linker driver; C source link inputs
              llvm.lld # links freestanding programs
              llvm.llvm # opt, llc, llvm-dis for looking at what the compiler writes
              pkgs.python3 # independent JSON diagnostic validation and benchmark scripts
              pkgs.time # peak compiler memory in scripts/benchmark_compile.py
            ];
            JIHOO_LLVM = "${llvm.llvm.lib}/lib/libLLVM-21.so";
            JIHOO_LD = "${llvm.lld}/bin/ld.lld";
            # The checkout's standard library, not the seed's.
            shellHook = ''
              export JIHOO_PATH=$PWD/lib
            '';
          };
        in
        {
          default = pkgs.mkShell shell;

          # All tools for agda/check.sh and agda/check-removal.sh, with the
          # same Horn input and Agda as the proof checks in CI.
          proofs = pkgs.mkShell (shell // {
            nativeBuildInputs = shell.nativeBuildInputs ++ [ pkgs.agda (hornCheckerFor pkgs) ];
            HORN = "${horn}";
          });

          # The default shell with QEMU, OVMF and the UEFI shell, which the
          # uefi suite of tests/runner.jh runs UEFI programs with (x86_64).
          uefi = pkgs.mkShell (shell // uefiTestEnv pkgs);

          # For working on the website in site/.
          site = pkgs.mkShell { packages = [ pkgs.nodejs ]; };
        });
    };
}
