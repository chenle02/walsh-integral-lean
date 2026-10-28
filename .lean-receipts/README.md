# Receipts

## `e0547e6`: lower-tier receipt, systemd unit walsh-integral-increments-20261028.service

- Receipt: `e0547e67d6a0-official-native.json`. systemd --user unit `walsh-integral-increments-20261028.service`, invocation `a84ff4242b2243b6b338a139a4e2c7f9` on `h-2db2e0fa6029`:
  Result success, exit `0`; runtime 00:11:02.58, CPU 00:12:13.70, memory peak 3.7 GiB; caps MemoryMax 12.0 GiB, MemorySwapMax 0 B, CPUQuota 200%, RuntimeMax 45min.
- Producer: lean-pkg 0.20.0 (installed), sources SHA-256 `558e6675cac80492b5ba57c2b12541b7cc408e6abf01b6cc7dc6b727fab8ea84`; unchanged from run start to collection.
- Checker: verify.sh (fresh complete library/reference/tests; all-owned/strict controls/native replay); sorry_count 0; axioms Classical.choice, Quot.sound, propext.
- Log: `e0547e67d6a0-systemd-user-walsh-integral-increments-20261028.service-a84ff4242b2243b6b338a139a4e2c7f9-h-2db2e0fa6029-verify.redacted.log.gz` (SHA-256 of decompressed log), SHA-256 `8bcd6712f8710d587470f60eaff5fc9b6bf7bc7d5333f2751deb4694fa3912f8` (= `report_sha256`);
  raw log SHA-256 `8bcd6712f8710d587470f60eaff5fc9b6bf7bc7d5333f2751deb4694fa3912f8` (0 line(s) differ: local paths redacted).
- Unit properties: `e0547e67d6a0-systemd-user-walsh-integral-increments-20261028.service-a84ff4242b2243b6b338a139a4e2c7f9-h-2db2e0fa6029-unit.properties`, SHA-256 `0952896983c3b63f4a9f81fa226cfe84685eab967a89d9cdab8bf2f4c7cec640` (captured before the unit was collected).
- Stored compressed: `e0547e67d6a0-systemd-user-walsh-integral-increments-20261028.service-a84ff4242b2243b6b338a139a4e2c7f9-h-2db2e0fa6029-verify.redacted.log.gz` (deterministic gzip, SHA-256 `63bd0afeb0acf1ab5ad24a8c2fdd26f49156310e7650c9e50df11955db649ef6` = `report_compressed.sha256`; 2574745 bytes uncompressed). Restore: `gzip -dc e0547e67d6a0-systemd-user-walsh-integral-increments-20261028.service-a84ff4242b2243b6b338a139a4e2c7f9-h-2db2e0fa6029-verify.redacted.log.gz > e0547e67d6a0-systemd-user-walsh-integral-increments-20261028.service-a84ff4242b2243b6b338a139a4e2c7f9-h-2db2e0fa6029-verify.redacted.log`, then `sha256sum e0547e67d6a0-systemd-user-walsh-integral-increments-20261028.service-a84ff4242b2243b6b338a139a4e2c7f9-h-2db2e0fa6029-verify.redacted.log` prints `report_sha256`.
- Seal: job stdout SHA-256 `5e573cca0bba92354f6165855525abf785a8a0f74742320fb453333e36e706b8` carries verify-log-sha256 = raw log SHA-256 `8bcd6712f8710d587470f60eaff5fc9b6bf7bc7d5333f2751deb4694fa3912f8`; lake-manifest.json SHA-256 `4613d80c583a8d8ce1176241cfdc90ca5fcb69677c83cef64d742db8a8e227d8` (pre = post).
