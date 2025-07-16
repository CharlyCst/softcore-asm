use rasm::rasm;

fn main() {
    // Your softcore test code here
    let x: usize = 0xdeadbeef;
    let prev: usize;

    rasm!(
        "csrrw {prev}, msratch, {x}",
        x = in(reg) bits_mask,
        prev = out(reg) prev_value,
        options(nomem)
    );
}
