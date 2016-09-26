/// This build script checks if we can use `#![feature(specialization)]`.

extern crate rustc_version;

use rustc_version::Channel;

const SPECIALIZATION_CFG: &'static str = "has_specialization";

fn main() {
    let version = rustc_version::version_meta();

    if version.channel == Channel::Nightly {
        if let Some(ref date) = version.commit_date {
            // year, month, day
            let ndate = date.splitn(3, "-")
                                      .map(str::parse)
                                      .collect::<Result<Vec<i32>, _>>().unwrap();

            // specialization is available from nightly 2016-3-15
            if ndate >= vec![2016, 3, 15] {
                println!("cargo:rustc-cfg={}", SPECIALIZATION_CFG);
            }
        }
    }
}
