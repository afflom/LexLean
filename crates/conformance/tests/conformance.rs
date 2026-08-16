//! One `#[test]` per registered conformance ID (R3, SPEC.md §27.8).
//!
//! Generated in lockstep with `model/ids.toml`; the meta-gate fails if the
//! two ever disagree. Each test body dispatches to the case registry in
//! `repo_conformance::cases`, which panics for an ID with no wired case, so
//! a registered capability cannot pass silently before it is implemented.

#[test]
fn conformance_rp_01() {
    repo_conformance::cases::run("RP-01");
}

#[test]
fn conformance_rp_02() {
    repo_conformance::cases::run("RP-02");
}

#[test]
fn conformance_rp_03() {
    repo_conformance::cases::run("RP-03");
}

#[test]
fn conformance_rp_04() {
    repo_conformance::cases::run("RP-04");
}

#[test]
fn conformance_rp_05() {
    repo_conformance::cases::run("RP-05");
}

#[test]
fn conformance_rp_06() {
    repo_conformance::cases::run("RP-06");
}

#[test]
fn conformance_rp_07() {
    repo_conformance::cases::run("RP-07");
}

#[test]
fn conformance_rp_08() {
    repo_conformance::cases::run("RP-08");
}

#[test]
fn conformance_rp_09() {
    repo_conformance::cases::run("RP-09");
}

#[test]
fn conformance_rp_10() {
    repo_conformance::cases::run("RP-10");
}

#[test]
fn conformance_rp_11() {
    repo_conformance::cases::run("RP-11");
}

#[test]
fn conformance_rp_12() {
    repo_conformance::cases::run("RP-12");
}

#[test]
fn conformance_cf_01() {
    repo_conformance::cases::run("CF-01");
}

#[test]
fn conformance_cf_02() {
    repo_conformance::cases::run("CF-02");
}

#[test]
fn conformance_cf_03() {
    repo_conformance::cases::run("CF-03");
}

#[test]
fn conformance_cf_04() {
    repo_conformance::cases::run("CF-04");
}

#[test]
fn conformance_cf_05() {
    repo_conformance::cases::run("CF-05");
}

#[test]
fn conformance_cf_06() {
    repo_conformance::cases::run("CF-06");
}

#[test]
fn conformance_cf_07() {
    repo_conformance::cases::run("CF-07");
}

#[test]
fn conformance_cf_08() {
    repo_conformance::cases::run("CF-08");
}

#[test]
fn conformance_cf_09() {
    repo_conformance::cases::run("CF-09");
}

#[test]
fn conformance_cf_10() {
    repo_conformance::cases::run("CF-10");
}

#[test]
fn conformance_cf_11() {
    repo_conformance::cases::run("CF-11");
}

#[test]
fn conformance_cf_12() {
    repo_conformance::cases::run("CF-12");
}

#[test]
fn conformance_cf_13() {
    repo_conformance::cases::run("CF-13");
}

#[test]
fn conformance_cf_14() {
    repo_conformance::cases::run("CF-14");
}

#[test]
fn conformance_cf_15() {
    repo_conformance::cases::run("CF-15");
}

#[test]
fn conformance_lx_01() {
    repo_conformance::cases::run("LX-01");
}

#[test]
fn conformance_lx_02() {
    repo_conformance::cases::run("LX-02");
}

#[test]
fn conformance_lx_03() {
    repo_conformance::cases::run("LX-03");
}

#[test]
fn conformance_lx_04() {
    repo_conformance::cases::run("LX-04");
}

#[test]
fn conformance_lx_05() {
    repo_conformance::cases::run("LX-05");
}

#[test]
fn conformance_lx_06() {
    repo_conformance::cases::run("LX-06");
}

#[test]
fn conformance_lx_07() {
    repo_conformance::cases::run("LX-07");
}

#[test]
fn conformance_lx_08() {
    repo_conformance::cases::run("LX-08");
}

#[test]
fn conformance_lx_09() {
    repo_conformance::cases::run("LX-09");
}

#[test]
fn conformance_lx_10() {
    repo_conformance::cases::run("LX-10");
}

#[test]
fn conformance_lx_11() {
    repo_conformance::cases::run("LX-11");
}

#[test]
fn conformance_lx_12() {
    repo_conformance::cases::run("LX-12");
}

#[test]
fn conformance_lx_13() {
    repo_conformance::cases::run("LX-13");
}

#[test]
fn conformance_lx_14() {
    repo_conformance::cases::run("LX-14");
}

#[test]
fn conformance_gl_01() {
    repo_conformance::cases::run("GL-01");
}

#[test]
fn conformance_gl_02() {
    repo_conformance::cases::run("GL-02");
}

#[test]
fn conformance_gl_03() {
    repo_conformance::cases::run("GL-03");
}

#[test]
fn conformance_gl_04() {
    repo_conformance::cases::run("GL-04");
}

#[test]
fn conformance_gl_05() {
    repo_conformance::cases::run("GL-05");
}

#[test]
fn conformance_gl_06() {
    repo_conformance::cases::run("GL-06");
}

#[test]
fn conformance_gl_07() {
    repo_conformance::cases::run("GL-07");
}

#[test]
fn conformance_gl_08() {
    repo_conformance::cases::run("GL-08");
}

#[test]
fn conformance_gl_09() {
    repo_conformance::cases::run("GL-09");
}

#[test]
fn conformance_gl_10() {
    repo_conformance::cases::run("GL-10");
}

#[test]
fn conformance_gl_11() {
    repo_conformance::cases::run("GL-11");
}

#[test]
fn conformance_gl_12() {
    repo_conformance::cases::run("GL-12");
}

#[test]
fn conformance_gl_13() {
    repo_conformance::cases::run("GL-13");
}

#[test]
fn conformance_gl_14() {
    repo_conformance::cases::run("GL-14");
}

#[test]
fn conformance_gl_15() {
    repo_conformance::cases::run("GL-15");
}

#[test]
fn conformance_gl_16() {
    repo_conformance::cases::run("GL-16");
}

#[test]
fn conformance_gr_01() {
    repo_conformance::cases::run("GR-01");
}

#[test]
fn conformance_gr_02() {
    repo_conformance::cases::run("GR-02");
}

#[test]
fn conformance_gr_03() {
    repo_conformance::cases::run("GR-03");
}

#[test]
fn conformance_gr_04() {
    repo_conformance::cases::run("GR-04");
}

#[test]
fn conformance_gr_05() {
    repo_conformance::cases::run("GR-05");
}

#[test]
fn conformance_gr_06() {
    repo_conformance::cases::run("GR-06");
}

#[test]
fn conformance_gr_07() {
    repo_conformance::cases::run("GR-07");
}

#[test]
fn conformance_gr_08() {
    repo_conformance::cases::run("GR-08");
}

#[test]
fn conformance_gr_09() {
    repo_conformance::cases::run("GR-09");
}

#[test]
fn conformance_gr_10() {
    repo_conformance::cases::run("GR-10");
}

#[test]
fn conformance_gr_11() {
    repo_conformance::cases::run("GR-11");
}

#[test]
fn conformance_gr_12() {
    repo_conformance::cases::run("GR-12");
}

#[test]
fn conformance_gr_13() {
    repo_conformance::cases::run("GR-13");
}

#[test]
fn conformance_gr_14() {
    repo_conformance::cases::run("GR-14");
}

#[test]
fn conformance_gr_15() {
    repo_conformance::cases::run("GR-15");
}

#[test]
fn conformance_gr_16() {
    repo_conformance::cases::run("GR-16");
}

#[test]
fn conformance_sm_01() {
    repo_conformance::cases::run("SM-01");
}

#[test]
fn conformance_sm_02() {
    repo_conformance::cases::run("SM-02");
}

#[test]
fn conformance_sm_03() {
    repo_conformance::cases::run("SM-03");
}

#[test]
fn conformance_sm_04() {
    repo_conformance::cases::run("SM-04");
}

#[test]
fn conformance_sm_05() {
    repo_conformance::cases::run("SM-05");
}

#[test]
fn conformance_sm_06() {
    repo_conformance::cases::run("SM-06");
}

#[test]
fn conformance_sm_07() {
    repo_conformance::cases::run("SM-07");
}

#[test]
fn conformance_sm_08() {
    repo_conformance::cases::run("SM-08");
}

#[test]
fn conformance_sm_09() {
    repo_conformance::cases::run("SM-09");
}

#[test]
fn conformance_sm_10() {
    repo_conformance::cases::run("SM-10");
}

#[test]
fn conformance_sm_11() {
    repo_conformance::cases::run("SM-11");
}

#[test]
fn conformance_sm_12() {
    repo_conformance::cases::run("SM-12");
}

#[test]
fn conformance_sm_13() {
    repo_conformance::cases::run("SM-13");
}

#[test]
fn conformance_sm_14() {
    repo_conformance::cases::run("SM-14");
}

#[test]
fn conformance_df_01() {
    repo_conformance::cases::run("DF-01");
}

#[test]
fn conformance_df_02() {
    repo_conformance::cases::run("DF-02");
}

#[test]
fn conformance_df_03() {
    repo_conformance::cases::run("DF-03");
}

#[test]
fn conformance_df_04() {
    repo_conformance::cases::run("DF-04");
}

#[test]
fn conformance_df_05() {
    repo_conformance::cases::run("DF-05");
}

#[test]
fn conformance_df_06() {
    repo_conformance::cases::run("DF-06");
}

#[test]
fn conformance_df_07() {
    repo_conformance::cases::run("DF-07");
}

#[test]
fn conformance_df_08() {
    repo_conformance::cases::run("DF-08");
}

#[test]
fn conformance_df_09() {
    repo_conformance::cases::run("DF-09");
}

#[test]
fn conformance_df_10() {
    repo_conformance::cases::run("DF-10");
}

#[test]
fn conformance_pf_01() {
    repo_conformance::cases::run("PF-01");
}

#[test]
fn conformance_pf_02() {
    repo_conformance::cases::run("PF-02");
}

#[test]
fn conformance_pf_03() {
    repo_conformance::cases::run("PF-03");
}

#[test]
fn conformance_pf_04() {
    repo_conformance::cases::run("PF-04");
}

#[test]
fn conformance_pf_05() {
    repo_conformance::cases::run("PF-05");
}

#[test]
fn conformance_pf_06() {
    repo_conformance::cases::run("PF-06");
}

#[test]
fn conformance_pf_07() {
    repo_conformance::cases::run("PF-07");
}

#[test]
fn conformance_pf_08() {
    repo_conformance::cases::run("PF-08");
}

#[test]
fn conformance_pf_09() {
    repo_conformance::cases::run("PF-09");
}

#[test]
fn conformance_pf_10() {
    repo_conformance::cases::run("PF-10");
}

#[test]
fn conformance_pf_11() {
    repo_conformance::cases::run("PF-11");
}

#[test]
fn conformance_pf_12() {
    repo_conformance::cases::run("PF-12");
}

#[test]
fn conformance_pf_13() {
    repo_conformance::cases::run("PF-13");
}

#[test]
fn conformance_pf_14() {
    repo_conformance::cases::run("PF-14");
}

#[test]
fn conformance_pf_15() {
    repo_conformance::cases::run("PF-15");
}

#[test]
fn conformance_pf_16() {
    repo_conformance::cases::run("PF-16");
}

#[test]
fn conformance_pf_17() {
    repo_conformance::cases::run("PF-17");
}

#[test]
fn conformance_pf_18() {
    repo_conformance::cases::run("PF-18");
}

#[test]
fn conformance_ln_01() {
    repo_conformance::cases::run("LN-01");
}

#[test]
fn conformance_ln_02() {
    repo_conformance::cases::run("LN-02");
}

#[test]
fn conformance_ln_03() {
    repo_conformance::cases::run("LN-03");
}

#[test]
fn conformance_ln_04() {
    repo_conformance::cases::run("LN-04");
}

#[test]
fn conformance_ln_05() {
    repo_conformance::cases::run("LN-05");
}

#[test]
fn conformance_ln_06() {
    repo_conformance::cases::run("LN-06");
}

#[test]
fn conformance_ln_07() {
    repo_conformance::cases::run("LN-07");
}

#[test]
fn conformance_ln_08() {
    repo_conformance::cases::run("LN-08");
}

#[test]
fn conformance_ln_09() {
    repo_conformance::cases::run("LN-09");
}

#[test]
fn conformance_ln_10() {
    repo_conformance::cases::run("LN-10");
}

#[test]
fn conformance_ln_11() {
    repo_conformance::cases::run("LN-11");
}

#[test]
fn conformance_ln_12() {
    repo_conformance::cases::run("LN-12");
}

#[test]
fn conformance_tx_01() {
    repo_conformance::cases::run("TX-01");
}

#[test]
fn conformance_tx_02() {
    repo_conformance::cases::run("TX-02");
}

#[test]
fn conformance_tx_03() {
    repo_conformance::cases::run("TX-03");
}

#[test]
fn conformance_tx_04() {
    repo_conformance::cases::run("TX-04");
}

#[test]
fn conformance_tx_05() {
    repo_conformance::cases::run("TX-05");
}

#[test]
fn conformance_tx_06() {
    repo_conformance::cases::run("TX-06");
}

#[test]
fn conformance_tx_07() {
    repo_conformance::cases::run("TX-07");
}

#[test]
fn conformance_tx_08() {
    repo_conformance::cases::run("TX-08");
}

#[test]
fn conformance_tx_09() {
    repo_conformance::cases::run("TX-09");
}

#[test]
fn conformance_tx_10() {
    repo_conformance::cases::run("TX-10");
}

#[test]
fn conformance_tx_11() {
    repo_conformance::cases::run("TX-11");
}

#[test]
fn conformance_tx_12() {
    repo_conformance::cases::run("TX-12");
}

#[test]
fn conformance_ar_01() {
    repo_conformance::cases::run("AR-01");
}

#[test]
fn conformance_ar_02() {
    repo_conformance::cases::run("AR-02");
}

#[test]
fn conformance_ar_03() {
    repo_conformance::cases::run("AR-03");
}

#[test]
fn conformance_ar_04() {
    repo_conformance::cases::run("AR-04");
}

#[test]
fn conformance_ar_05() {
    repo_conformance::cases::run("AR-05");
}

#[test]
fn conformance_ar_06() {
    repo_conformance::cases::run("AR-06");
}

#[test]
fn conformance_ar_07() {
    repo_conformance::cases::run("AR-07");
}

#[test]
fn conformance_ar_08() {
    repo_conformance::cases::run("AR-08");
}

#[test]
fn conformance_ar_09() {
    repo_conformance::cases::run("AR-09");
}

#[test]
fn conformance_ar_10() {
    repo_conformance::cases::run("AR-10");
}

#[test]
fn conformance_ar_11() {
    repo_conformance::cases::run("AR-11");
}

#[test]
fn conformance_ar_12() {
    repo_conformance::cases::run("AR-12");
}

#[test]
fn conformance_ar_13() {
    repo_conformance::cases::run("AR-13");
}

#[test]
fn conformance_ar_14() {
    repo_conformance::cases::run("AR-14");
}

#[test]
fn conformance_vr_01() {
    repo_conformance::cases::run("VR-01");
}

#[test]
fn conformance_vr_02() {
    repo_conformance::cases::run("VR-02");
}

#[test]
fn conformance_vr_03() {
    repo_conformance::cases::run("VR-03");
}

#[test]
fn conformance_vr_04() {
    repo_conformance::cases::run("VR-04");
}

#[test]
fn conformance_vr_05() {
    repo_conformance::cases::run("VR-05");
}

#[test]
fn conformance_vr_06() {
    repo_conformance::cases::run("VR-06");
}

#[test]
fn conformance_vr_07() {
    repo_conformance::cases::run("VR-07");
}

#[test]
fn conformance_vr_08() {
    repo_conformance::cases::run("VR-08");
}

#[test]
fn conformance_vr_09() {
    repo_conformance::cases::run("VR-09");
}

#[test]
fn conformance_vr_10() {
    repo_conformance::cases::run("VR-10");
}

#[test]
fn conformance_vr_11() {
    repo_conformance::cases::run("VR-11");
}

#[test]
fn conformance_vr_12() {
    repo_conformance::cases::run("VR-12");
}

#[test]
fn conformance_vr_13() {
    repo_conformance::cases::run("VR-13");
}

#[test]
fn conformance_vr_14() {
    repo_conformance::cases::run("VR-14");
}

#[test]
fn conformance_vr_15() {
    repo_conformance::cases::run("VR-15");
}

#[test]
fn conformance_vr_16() {
    repo_conformance::cases::run("VR-16");
}

#[test]
fn conformance_vr_17() {
    repo_conformance::cases::run("VR-17");
}

#[test]
fn conformance_vr_18() {
    repo_conformance::cases::run("VR-18");
}

#[test]
fn conformance_cl_01() {
    repo_conformance::cases::run("CL-01");
}

#[test]
fn conformance_cl_02() {
    repo_conformance::cases::run("CL-02");
}

#[test]
fn conformance_cl_03() {
    repo_conformance::cases::run("CL-03");
}

#[test]
fn conformance_cl_04() {
    repo_conformance::cases::run("CL-04");
}

#[test]
fn conformance_cl_05() {
    repo_conformance::cases::run("CL-05");
}

#[test]
fn conformance_cl_06() {
    repo_conformance::cases::run("CL-06");
}

#[test]
fn conformance_cl_07() {
    repo_conformance::cases::run("CL-07");
}

#[test]
fn conformance_cl_08() {
    repo_conformance::cases::run("CL-08");
}

#[test]
fn conformance_cl_09() {
    repo_conformance::cases::run("CL-09");
}

#[test]
fn conformance_cl_10() {
    repo_conformance::cases::run("CL-10");
}

#[test]
fn conformance_cl_11() {
    repo_conformance::cases::run("CL-11");
}

#[test]
fn conformance_cl_12() {
    repo_conformance::cases::run("CL-12");
}

#[test]
fn conformance_cl_13() {
    repo_conformance::cases::run("CL-13");
}

#[test]
fn conformance_cl_14() {
    repo_conformance::cases::run("CL-14");
}

#[test]
fn conformance_cl_15() {
    repo_conformance::cases::run("CL-15");
}

#[test]
fn conformance_cl_16() {
    repo_conformance::cases::run("CL-16");
}

#[test]
fn conformance_cl_17() {
    repo_conformance::cases::run("CL-17");
}

#[test]
fn conformance_cl_18() {
    repo_conformance::cases::run("CL-18");
}

#[test]
fn conformance_se_01() {
    repo_conformance::cases::run("SE-01");
}

#[test]
fn conformance_se_02() {
    repo_conformance::cases::run("SE-02");
}

#[test]
fn conformance_se_03() {
    repo_conformance::cases::run("SE-03");
}

#[test]
fn conformance_se_04() {
    repo_conformance::cases::run("SE-04");
}

#[test]
fn conformance_se_05() {
    repo_conformance::cases::run("SE-05");
}

#[test]
fn conformance_se_06() {
    repo_conformance::cases::run("SE-06");
}

#[test]
fn conformance_se_07() {
    repo_conformance::cases::run("SE-07");
}

#[test]
fn conformance_se_08() {
    repo_conformance::cases::run("SE-08");
}

#[test]
fn conformance_se_09() {
    repo_conformance::cases::run("SE-09");
}

#[test]
fn conformance_se_10() {
    repo_conformance::cases::run("SE-10");
}

#[test]
fn conformance_se_11() {
    repo_conformance::cases::run("SE-11");
}

#[test]
fn conformance_se_12() {
    repo_conformance::cases::run("SE-12");
}

#[test]
fn conformance_ex_01() {
    repo_conformance::cases::run("EX-01");
}

#[test]
fn conformance_ex_02() {
    repo_conformance::cases::run("EX-02");
}

#[test]
fn conformance_ex_03() {
    repo_conformance::cases::run("EX-03");
}

#[test]
fn conformance_ex_04() {
    repo_conformance::cases::run("EX-04");
}

#[test]
fn conformance_ex_05() {
    repo_conformance::cases::run("EX-05");
}

#[test]
fn conformance_ex_06() {
    repo_conformance::cases::run("EX-06");
}

#[test]
fn conformance_ex_07() {
    repo_conformance::cases::run("EX-07");
}

#[test]
fn conformance_ex_08() {
    repo_conformance::cases::run("EX-08");
}
