/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2467 : Family 10 := level10.get ⟨1550,by decide⟩
def sourceMap2467 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (sourceLabel 10 0 0 v)
def fusedMap2467 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2467_checked : acceptsGraphIso
    (source (graph core2467) (root 10) 0 0) DegreeOneSmallSpectrum2002.graph sourceMap2467=true := by decide +kernel
theorem fusedMap2467_checked : acceptsGraphIso
    (fused (graph core2467) (root 10) 0 0) DegreeOneSmallSpectrum1569.graph fusedMap2467=true := by decide +kernel
theorem certified2467 : Certified (graph core2467) (root 10) 0 0 :=
  of_native_maps core2467 DegreeOneSmallSpectrum2002.graph DegreeOneSmallSpectrum1569.graph
    sourceMap2467 fusedMap2467 sourceMap2467_checked fusedMap2467_checked
    DegreeOneSmallComparisons.comparison2467
#print axioms sourceMap2467_checked
#print axioms fusedMap2467_checked
#print axioms certified2467
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
