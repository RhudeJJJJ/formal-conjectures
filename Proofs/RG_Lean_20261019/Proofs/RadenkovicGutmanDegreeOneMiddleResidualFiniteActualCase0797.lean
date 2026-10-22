/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0797 : Family 10 := level10.get ⟨473,by decide⟩
def sourceMap0797 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0797 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0797_checked : acceptsGraphIso
    (source (graph core0797) (root 10) 2 2) DegreeTwoThreeSpectrum6860.graph sourceMap0797=true := by decide +kernel
theorem fusedMap0797_checked : acceptsGraphIso
    (fused (graph core0797) (root 10) 2 2) DegreeTwoThreeSpectrum5933.graph fusedMap0797=true := by decide +kernel
theorem certified0797 : Certified (graph core0797) (root 10) 2 2 :=
  of_native_maps core0797 DegreeTwoThreeSpectrum6860.graph DegreeTwoThreeSpectrum5933.graph
    sourceMap0797 fusedMap0797 sourceMap0797_checked fusedMap0797_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0797
#print axioms sourceMap0797_checked
#print axioms fusedMap0797_checked
#print axioms certified0797
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
