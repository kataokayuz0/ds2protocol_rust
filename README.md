The functions used in each process (gen, sign, verify) in the DS2 protocol are described in src/bin/gen.rs, sign.rs, verify.rs.

To actually run the entire protocol, run src/bin/ds2.rs with the command cargo run --bin ds2.

![This process creates a share of the public and private keys, respectively.](image/ds2gen.png "DS2_gen")

![In this process, each party creates its own signature share, and the entire protocol generates signatures.](image/ds2sign.png "DS2_sign")

![This process performs verification of the signatures containing the commitments.](image/ds2verify.png "DS2_verify")
