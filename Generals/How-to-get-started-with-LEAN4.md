# How to get started with LEAN4 for formal mathematics

What is lean4 ?

### Linux Machine + VS code Setup

1. Pre-requisites - Make sure following modules are present onto your machine

   ```
   sudo apt update && sudo apt install git curl wget unzip python3 python3-pip -y

   ```
2. VS Code - Download and Install the visual studio code from : https://code.visualstudio.com and Lean4 Prover Extension from : https://marketplace.visualstudio.com/items?itemName=leanprover.lean4
3. Lean toolchain manager that manages the multiple lean versions similar to rust up for rust

   ```
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

   ```
4. Verify that elan installed onto the machine : `elan --version`
5. installation of latest stable Lean4 build
```
   elan toolchain install leanprover/lean4:stable
   elan default leanprover/lean4:stable

   # Output

   lean4:stable
   info: default toolchain set to 'leanprover/lean4:stable'
```
6. Verify the installation : `lean --version`
7. Let's check the all installed versions : `elan show`

   ```plaintext
   installed toolchains
   --------------------

   leanprover/lean4:v4.18.0
   leanprover/lean4:v4.24.0 (resolved from default 'leanprover/lean4:stable')

   active toolchain
   ----------------

   leanprover/lean4:v4.24.0 (resolved from default 'leanprover/lean4:stable')
   Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)
   ```
