/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0608 : Family 10 := level10.get ⟨160,by decide⟩
def sourceMap0608 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0608 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0608_checked : acceptsGraphIso
    (source (graph core0608) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1872.graph sourceMap0608=true := by decide +kernel
theorem fusedMap0608_checked : acceptsGraphIso
    (fused (graph core0608) (root 10) 2 2) DegreeTwoThreeSpectrum5098.graph fusedMap0608=true := by decide +kernel
theorem certified0608 : Certified (graph core0608) (root 10) 2 2 :=
  of_native_maps core0608 DegreeOneMiddleResidualSpectrum1872.graph DegreeTwoThreeSpectrum5098.graph
    sourceMap0608 fusedMap0608 sourceMap0608_checked fusedMap0608_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0608
#print axioms sourceMap0608_checked
#print axioms fusedMap0608_checked
#print axioms certified0608
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
