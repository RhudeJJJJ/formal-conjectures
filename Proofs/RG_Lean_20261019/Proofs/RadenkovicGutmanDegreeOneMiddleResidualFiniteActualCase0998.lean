/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0998 : Family 10 := level10.get ⟨884,by decide⟩
def sourceMap0998 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0998 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0998_checked : acceptsGraphIso
    (source (graph core0998) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2301.graph sourceMap0998=true := by decide +kernel
theorem fusedMap0998_checked : acceptsGraphIso
    (fused (graph core0998) (root 10) 2 2) DegreeTwoThreeSpectrum5738.graph fusedMap0998=true := by decide +kernel
theorem certified0998 : Certified (graph core0998) (root 10) 2 2 :=
  of_native_maps core0998 DegreeOneMiddleResidualSpectrum2301.graph DegreeTwoThreeSpectrum5738.graph
    sourceMap0998 fusedMap0998 sourceMap0998_checked fusedMap0998_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0998
#print axioms sourceMap0998_checked
#print axioms fusedMap0998_checked
#print axioms certified0998
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
