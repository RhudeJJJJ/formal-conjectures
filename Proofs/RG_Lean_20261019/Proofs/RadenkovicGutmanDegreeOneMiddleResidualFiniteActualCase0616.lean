/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0616 : Family 10 := level10.get ⟨173,by decide⟩
def sourceMap0616 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0616 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0616_checked : acceptsGraphIso
    (source (graph core0616) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1873.graph sourceMap0616=true := by decide +kernel
theorem fusedMap0616_checked : acceptsGraphIso
    (fused (graph core0616) (root 10) 2 2) DegreeTwoThreeSpectrum5117.graph fusedMap0616=true := by decide +kernel
theorem certified0616 : Certified (graph core0616) (root 10) 2 2 :=
  of_native_maps core0616 DegreeOneMiddleResidualSpectrum1873.graph DegreeTwoThreeSpectrum5117.graph
    sourceMap0616 fusedMap0616 sourceMap0616_checked fusedMap0616_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0616
#print axioms sourceMap0616_checked
#print axioms fusedMap0616_checked
#print axioms certified0616
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
