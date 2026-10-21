/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2313 : Family 10 := level10.get ⟨1000,by decide⟩
def sourceMap2313 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2313 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2313_checked : acceptsGraphIso
    (source (graph core2313) (root 10) 0 0) DegreeOneSmallSpectrum1538.graph sourceMap2313=true := by decide +kernel
theorem fusedMap2313_checked : acceptsGraphIso
    (fused (graph core2313) (root 10) 0 0) DegreeOneSmallSpectrum1540.graph fusedMap2313=true := by decide +kernel
theorem certified2313 : Certified (graph core2313) (root 10) 0 0 :=
  of_native_maps core2313 DegreeOneSmallSpectrum1538.graph DegreeOneSmallSpectrum1540.graph
    sourceMap2313 fusedMap2313 sourceMap2313_checked fusedMap2313_checked
    DegreeOneSmallComparisons.comparison2313
#print axioms sourceMap2313_checked
#print axioms fusedMap2313_checked
#print axioms certified2313
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
