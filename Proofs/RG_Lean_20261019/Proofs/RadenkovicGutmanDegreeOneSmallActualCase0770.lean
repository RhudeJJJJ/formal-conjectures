/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0770 : Family 8 := level8.get ⟨9,by decide⟩
def sourceMap0770 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0770 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0770_checked : acceptsGraphIso
    (source (graph core0770) (root 8) 1 1) DegreeOneSmallSpectrum1166.graph sourceMap0770=true := by decide +kernel
theorem fusedMap0770_checked : acceptsGraphIso
    (fused (graph core0770) (root 8) 1 1) DegreeOneSmallSpectrum879.graph fusedMap0770=true := by decide +kernel
theorem certified0770 : Certified (graph core0770) (root 8) 1 1 :=
  of_native_maps core0770 DegreeOneSmallSpectrum1166.graph DegreeOneSmallSpectrum879.graph
    sourceMap0770 fusedMap0770 sourceMap0770_checked fusedMap0770_checked
    DegreeOneSmallComparisons.comparison0770
#print axioms sourceMap0770_checked
#print axioms fusedMap0770_checked
#print axioms certified0770
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
