/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0770 : Family 10 := level10.get ⟨420,by decide⟩
def sourceMap0770 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0770 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0770_checked : acceptsGraphIso
    (source (graph core0770) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1863.graph sourceMap0770=true := by decide +kernel
theorem fusedMap0770_checked : acceptsGraphIso
    (fused (graph core0770) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1460.graph fusedMap0770=true := by decide +kernel
theorem certified0770 : Certified (graph core0770) (root 10) 2 2 :=
  of_native_maps core0770 DegreeOneMiddleResidualSpectrum1863.graph DegreeOneMiddleResidualSpectrum1460.graph
    sourceMap0770 fusedMap0770 sourceMap0770_checked fusedMap0770_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0770
#print axioms sourceMap0770_checked
#print axioms fusedMap0770_checked
#print axioms certified0770
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
