def warn_unknown_bsc_diag_option : Warning<
    "unknown %select{warning|remark|error}0 option '%1'%select{|; did you mean '%3'?}2">,
    InGroup<UnknownWarningOption>;