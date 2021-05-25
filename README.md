# quic-dafny

This repo contains code for the Dafny implementation of QUIC protocol layer, which is used in the following paper:

[A Security Model and Fully Verified Implementation for the IETF QUIC Record Layer](http://www.andrew.cmu.edu/user/bparno/papers/quic-record.pdf)
Antoine Delignat-Lavaud, Cédric Fournet, Bryan Parno, Jonathan Protzenko, Tahina Ramananandro, Jay Bosamiya, Joseph Lallemand, Itsaka Rakotonirina, and Yi Zhou
In Proceedings of the IEEE Symposium on Security and Privacy, May, 2021

The F* implementation of QUIC record layer can be found in the [everquic repo](https://github.com/project-everest/everquic-crypto).

This work was done as part of [Project Everest](https://project-everest.github.io/).

## How to Build

Simply run `make` on the current directory. This should automatically run everything necessary to build all the files.

## How to Verify

Run `make verify` on the current directory.

## Code Guide

### Dafny sources

All the Dafny files are `.dfy` files in the `src/` directory. They can be grouped as:

+ **Connection Management:** QUICConnection, QUICAPIs, QEngine, QUICEngine, QPacketSpace, QUICDataTypes, QConnection, QUICTLS
+ **Data Structures:** Seqs, PrivateDLL, FreezableArray, DynamicArray
+ **Frame mgmt:** QUICConstants, QUICUtils, QUICFrame
+ **Loss Recovery and Congestion Control:** QLossRecovery, QUICLossAndCongestion
+ **Stream mgmt:** QStream, QUICStream, QStreamManager
+ **Miscellaneous:**: OverFlowCheck, Options, Misc
+ **FFI:** HandleFFIs, QUICFFI, Extern, NativeTypes, QUICCrypto

### FFI connectors

These are hand-written `.h` and `.cpp` files used for FFI. They can be
found in `ffi-connections/` and `src/handwritten-dot-h-files/`
directories.

### Example client and server

These handwritten files can be found in the `examples/` directory. For
testing see the `data/` directory.

For conveniently testing and benchmarking the generated server and
client, see the `scripts/` directory.

### Extracted code from miTLS, mipki, everquic

Can be found in their respective directories. 
