{
  description = "jihoo: a systems language as fast as C, memory-safe without lifetimes";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      lib = nixpkgs.lib;
      systems = [ "x86_64-linux" "aarch64-linux" ];
      forAllSystems = f: lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      version = "0.5.0";

      # Only what the compiler needs, so that editing the website (or docs)
      # does not rebuild it.
      sources = lib.fileset.unions [
        ./compiler
        ./lib
        ./examples
        ./tests
      ];
      src = lib.fileset.toSource {
        root = ./.;
        fileset = sources;
      };

      # The tests also read the pages they check against the compiler. Editing
      # these reruns the tests, and does not rebuild the compiler.
      testSrc = lib.fileset.toSource {
        root = ./.;
        fileset = lib.fileset.unions [
          sources
          ./scripts/benchmark_compile.py
          ./docs/internals/core-spec.md
          ./docs/language/dependent-types.md
          ./docs/language/dependent-functions.md
          ./docs/language/dependent-aliases.md
          ./docs/language/dependent-records.md
          ./docs/language/proof-automation.md
          ./docs/language/buffer-ranges.md
          ./docs/language/bounded-collection.md
          ./docs/language/list-buffer-transfer.md
          ./docs/language/vector-extension.md
        ];
      };

      # The seed: exact release archives checked into bootstrap/, so builds do
      # not depend on GitHub Release downloads. compiler/ and its imports use only
      # what the seed knows; to use something new there, release the compiler
      # that has it and move the seed here.
      seed = {
        version = "0.5.0";
        hash = {
          x86_64-linux = "sha256-qf7crmzcURQvHSb8aUuqSMaGNvqbOeq3d7Rd0xNOytw=";
          aarch64-linux = "sha256-O7FbHo4fauiNVMbjb7LM6eG1rLPws3Gi0r8ahW0zohE=";
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
            src = builtins.path {
              path = ./bootstrap + "/jihoo-${pkgs.stdenv.hostPlatform.system}.tar.gz";
              name = "jihoo-v${seed.version}-${pkgs.stdenv.hostPlatform.system}.tar.gz";
              recursive = false;
              sha256 = seed.hash.${pkgs.stdenv.hostPlatform.system};
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
        in
        {
          # tests/runner.jh, built and run by the installed compiler, tests
          # it: the programs of tests/run, tests/fail and examples, the
          # backend, that it builds a compiler that writes the same IR, and
          # UEFI programs in QEMU.
          # Independent specification fragment, not a verified compiler.
          # The toolchain version is checked against proofs/lean-toolchain.
          lean-proofs = pkgs.runCommand "jihoo-lean-proofs" {
            nativeBuildInputs = [ pkgs.lean4 pkgs.python3 ];
          } ''
            cp -r ${lib.fileset.toSource {
              root = ./proofs;
              fileset = lib.fileset.unions [
                ./proofs/Jihoo
                ./proofs/Jihoo.lean
                ./proofs/Audit.lean
                ./proofs/EmitMixedProofTranslation.lean
                ./proofs/EmitMixedInference.lean
                ./proofs/EmitMixedTelescope.lean
                ./proofs/EmitCore.lean
                ./proofs/EmitPrimitiveSafety.lean
                ./proofs/EmitBinderClassification.lean
                ./proofs/lean-toolchain
                ./proofs/lakefile.toml
                ./proofs/lake-manifest.json
                ./proofs/check.sh
              ];
            }} proofs
            chmod -R u+w proofs
            mkdir -p tests/core_preserves
            cp ${./tests/core_preserves/lean-core-translation.jhc} tests/core_preserves/lean-core-translation.jhc
            cp ${./tests/core_preserves/lean-primitive-safety.jhc} tests/core_preserves/lean-primitive-safety.jhc
            cp ${./tests/core_preserves/lean-mixed-telescope.jhc} tests/core_preserves/lean-mixed-telescope.jhc
            cp ${./tests/core_mixed_inference.tsv} tests/core_mixed_inference.tsv
            cp ${./tests/core_preserves/lean-mixed-proof-translation.jhc} tests/core_preserves/lean-mixed-proof-translation.jhc
            cp ${./tests/core_binder_modes.txt} tests/core_binder_modes.txt
            bash proofs/check.sh
            touch $out
          '';

          # Build the exporter against this exact compiler/core.jh, execute
          # real transforms, and feed their snapshots to the Lean validator.
          # Replay imports the exact retained canonical artifact and validates
          # whole-graph/root continuity before any subsequent consumer runs.
          # This is an integration check, not a proof of importer/exporter fidelity.
          graph-certificates = pkgs.runCommand "jihoo-graph-certificates" {
            nativeBuildInputs = [ jihoo pkgs.lean4 pkgs.python3 ];
          } ''
            cp -r ${lib.fileset.toSource {
              root = ./.;
              fileset = lib.fileset.unions [
                sources
                ./proofs/Jihoo
                ./proofs/Jihoo.lean
                ./proofs/CheckGraph.lean
                ./proofs/CheckArtifact.lean
                ./proofs/CheckMixedProof.lean
                ./proofs/CheckMixedRaw.lean
                ./proofs/CheckTyping.lean
                ./proofs/CheckBetaReplay.lean
                ./proofs/CheckEvidence.lean
                ./proofs/CheckNormalization.lean
                ./proofs/CheckTypeNormalization.lean
                ./proofs/CheckCoreNormal.lean
                ./proofs/CheckLinearNormal.lean
                ./proofs/CheckLinearEvidence.lean
                ./proofs/CheckCorePrincipal.lean
                ./proofs/CheckFirstOrderApplication.lean
                ./proofs/CheckApplicationSpine.lean
                ./proofs/CheckPropositionalEvidence.lean
                ./proofs/lean-toolchain
                ./proofs/lakefile.toml
                ./proofs/lake-manifest.json
              ];
            }} source
            chmod -R u+w source
            cd source
            export JIHOO_PATH=$PWD/lib
            (cd proofs && lake build --wfail)
            python3 tests/core_initialization_proof.py --compiler ${jihoo}/bin/jihoo
            python3 -O tests/core_initialization_proof.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_call_machine.py --compiler ${jihoo}/bin/jihoo
            python3 -O tests/core_call_machine.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_producer_gates.py
            python3 tests/core_transform_certificates.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_artifact_replay.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_mixed_proof_admission.py --compiler ${jihoo}/bin/jihoo
            python3 -O tests/core_mixed_proof_admission.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_mixed_raw.py --compiler ${jihoo}/bin/jihoo
            python3 -O tests/core_mixed_raw.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_typing_certificates.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_typed_beta_replay.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_literal_evidence.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_head_normalization.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_type_index_normalization.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_checked_normalization.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_linear_normalization.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_linear_evidence.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_principal_evidence.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_first_order_application.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_application_spine.py --compiler ${jihoo}/bin/jihoo
            python3 -O tests/core_application_spine.py --compiler ${jihoo}/bin/jihoo
            python3 tests/core_propositional_evidence.py --compiler ${jihoo}/bin/jihoo
            python3 -O tests/core_propositional_evidence.py --compiler ${jihoo}/bin/jihoo
            touch $out
          '';

          tests = pkgs.stdenv.mkDerivation ({
            pname = "jihoo-tests";
            inherit version;
            src = testSrc;
            nativeBuildInputs = [ jihoo llvm.clang llvm.lld pkgs.python3 pkgs.time ];
            dontConfigure = true;
            buildPhase = ''
              export JIHOO_PATH=$PWD/lib JIHOO_COMPILER=${jihoo}/bin/jihoo
              jihoo run tests/runner.jh
              python3 tests/dependent_benchmark.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_primitive_safety.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_quantities.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_erasure_traces.py --compiler ${jihoo}/bin/jihoo
              python3 -O tests/core_erasure_traces.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_capture_environment.py --compiler ${jihoo}/bin/jihoo
              python3 -O tests/core_capture_environment.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_symbols.py --compiler ${jihoo}/bin/jihoo
              python3 -O tests/core_symbols.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_call_entry.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_binder_projection.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_lend_projection.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_proof_functions.py --compiler ${jihoo}/bin/jihoo
              python3 -O tests/core_proof_functions.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_mixed_telescope.py --compiler ${jihoo}/bin/jihoo
              python3 tests/core_type_family_safety.py --compiler ${jihoo}/bin/jihoo
            '';
            installPhase = "touch $out";
          } // uefiTestEnv pkgs);

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

          # The default shell with QEMU, OVMF and the UEFI shell, which the
          # uefi suite of tests/runner.jh runs UEFI programs with (x86_64).
          uefi = pkgs.mkShell (shell // uefiTestEnv pkgs);

          # For working on the website in site/.
          site = pkgs.mkShell { packages = [ pkgs.nodejs ]; };
        });
    };
}
