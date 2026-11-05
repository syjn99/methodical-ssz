import Kraken.FunSpec

-- The state named by `funspec ... at s` precedes the return-address push.
theorem review_funspec_spill_address (s : MachineData) (ret : Int64) :
    (s.push64 ret).regs.rsp.toBitVec + 16 = s.regs.rsp.toBitVec + 8 := by
  change s.regs.rsp.toBitVec - 8 + 16 = s.regs.rsp.toBitVec + 8
  bv_omega

#print axioms review_funspec_spill_address
