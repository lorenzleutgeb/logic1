# SMT-LIB

## How to Download

Use `make` to populate subdirectories.

To populate a particular subdirectory, e.g. `FOO`, use `make FOO/`.
This will download `FOO.tar.zst` and compare the checksum against `FOO.tar.zst.md5sum`.

The logics to download are defined by creating `*.tar.zst.md5sum` files.

## How to Update

 1. Select desired record from
    <https://zenodo.org/communities/smt-lib/records?q=release&sort=publication-desc>,
 2. Update `Makefile` to refer to the record chosen.
 3. For each desired logic, manually copy the MD5 checksum from the Zenodo overview page
    of the record, e.g. <https://zenodo.org/records/16740866#record-files>, and create
    a corresponding `*.tar.zst.md5sum` file.
