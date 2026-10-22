/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0057 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0057 : (Vertices 3 ⊕ Fin 5 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,11,12,13,1,2,3,4,5,6,7,8,9,10] (sourceLabel 3 4 4 v)
def fusedMap0057 : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12,13] (fusedLabel 3 4 4 v)
theorem sourceMap0057_checked : acceptsGraphIso
    (source (graph core0057) (root 3) 4 4) DegreeOneMiddleResidualSpectrum055.graph sourceMap0057=true := by decide +kernel
theorem fusedMap0057_checked : acceptsGraphIso
    (fused (graph core0057) (root 3) 4 4) DegreeOneMiddleResidualSpectrum000.graph fusedMap0057=true := by decide +kernel
theorem certified0057 : Certified (graph core0057) (root 3) 4 4 :=
  of_native_maps core0057 DegreeOneMiddleResidualSpectrum055.graph DegreeOneMiddleResidualSpectrum000.graph
    sourceMap0057 fusedMap0057 sourceMap0057_checked fusedMap0057_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0057
#print axioms sourceMap0057_checked
#print axioms fusedMap0057_checked
#print axioms certified0057
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
