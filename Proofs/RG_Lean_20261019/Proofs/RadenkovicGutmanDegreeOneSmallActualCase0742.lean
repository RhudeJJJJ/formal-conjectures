/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0742 : Family 8 := level8.get ⟨1,by decide⟩
def sourceMap0742 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0742 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0742_checked : acceptsGraphIso
    (source (graph core0742) (root 8) 1 1) DegreeOneSmallSpectrum896.graph sourceMap0742=true := by decide +kernel
theorem fusedMap0742_checked : acceptsGraphIso
    (fused (graph core0742) (root 8) 1 1) DegreeOneSmallSpectrum856.graph fusedMap0742=true := by decide +kernel
theorem certified0742 : Certified (graph core0742) (root 8) 1 1 :=
  of_native_maps core0742 DegreeOneSmallSpectrum896.graph DegreeOneSmallSpectrum856.graph
    sourceMap0742 fusedMap0742 sourceMap0742_checked fusedMap0742_checked
    DegreeOneSmallComparisons.comparison0742
#print axioms sourceMap0742_checked
#print axioms fusedMap0742_checked
#print axioms certified0742
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
