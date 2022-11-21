# Recommended environment:

Linux/macOS/WSL (System) + VSCode (Editor) + VSCoq (Plugin)

    sudo apt install opam

# Recommended Coq installation:

https://coq.inria.fr/opam-using.html

    all_proxy=socks5://192.168.1.254 opam switch create coq-8.15.0 ocaml-system.4.08.1
    opam init
    eval $(opam env)
    opam pin add coq 8.15.0

# Download and Build Logical Foundations

    wget https://softwarefoundations.cis.upenn.edu/lf-current/lf.tgz
    tar -xzvf lf.tgz
    cd lf
    make
    code .

alt + down
alt + right
