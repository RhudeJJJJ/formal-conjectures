/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFinitePrerequisites
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch000
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch001
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch002
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch003
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch004
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch005
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch006
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch007
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch008
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch009
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch010
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch011
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch012
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch013
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch014
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch015
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch016
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch017
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch018
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch019
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch020
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch021
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch022
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch023
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCertificateBatch024
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteAllCertificates
open SmallGeFourKeys DegreeOneMiddleResidualFiniteKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem certified_all_keys : ∀ (k : SmallGeFourKeys.Key), k ∈ DegreeOneMiddleResidualFiniteKeys.keys → SmallGeFourKeys.Certified k := by
  intro k hk
  simp only [DegreeOneMiddleResidualFiniteKeys.keys,List.mem_append,List.not_mem_nil,or_false] at hk
  rcases hk with h000 | h001 | h002 | h003 | h004 | h005 | h006 | h007 | h008 | h009 | h010 | h011 | h012 | h013 | h014 | h015 | h016 | h017 | h018 | h019 | h020 | h021 | h022 | h023 | h024
  · exact certified_keys000 k h000
  · exact certified_keys001 k h001
  · exact certified_keys002 k h002
  · exact certified_keys003 k h003
  · exact certified_keys004 k h004
  · exact certified_keys005 k h005
  · exact certified_keys006 k h006
  · exact certified_keys007 k h007
  · exact certified_keys008 k h008
  · exact certified_keys009 k h009
  · exact certified_keys010 k h010
  · exact certified_keys011 k h011
  · exact certified_keys012 k h012
  · exact certified_keys013 k h013
  · exact certified_keys014 k h014
  · exact certified_keys015 k h015
  · exact certified_keys016 k h016
  · exact certified_keys017 k h017
  · exact certified_keys018 k h018
  · exact certified_keys019 k h019
  · exact certified_keys020 k h020
  · exact certified_keys021 k h021
  · exact certified_keys022 k h022
  · exact certified_keys023 k h023
  · exact certified_keys024 k h024
theorem certificates : DegreeOneMiddleResidualFiniteTransfer.Certificates := by
  intro n i p q hk
  exact certified_all_keys ⟨n,i,p,q⟩ hk
theorem residual_cases : DegreeOneMiddleAnchors.ResidualCases :=
  DegreeOneMiddleResidualFiniteTransfer.residual_cases_of_certificates certificates
#print axioms residual_cases
#print axioms certified_all_keys
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteAllCertificates
