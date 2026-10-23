extern fn aligned(value: const i64&) = "gs_test_aligned";
var wide: i64 = 100;
fn next_wide() -> i64 { aligned(wide); wide += 1; wide }
