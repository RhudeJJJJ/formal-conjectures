/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0308 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0308 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,6,2,3,4,5] (sourceLabel 6 1 1 v)
def fusedMap0308 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0308_checked : acceptsGraphIso
    (source (graph core0308) (root 6) 1 1) DegreeOneSmallSpectrum199.graph sourceMap0308=true := by decide +kernel
theorem fusedMap0308_checked : acceptsGraphIso
    (fused (graph core0308) (root 6) 1 1) DegreeOneSmallSpectrum167.graph fusedMap0308=true := by decide +kernel
theorem certified0308 : Certified (graph core0308) (root 6) 1 1 :=
  of_native_maps core0308 DegreeOneSmallSpectrum199.graph DegreeOneSmallSpectrum167.graph
    sourceMap0308 fusedMap0308 sourceMap0308_checked fusedMap0308_checked
    DegreeOneSmallComparisons.comparison0308
#print axioms sourceMap0308_checked
#print axioms fusedMap0308_checked
#print axioms certified0308
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
