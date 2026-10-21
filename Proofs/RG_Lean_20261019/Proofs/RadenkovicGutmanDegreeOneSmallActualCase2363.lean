/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2363 : Family 10 := level10.get ⟨1114,by decide⟩
def sourceMap2363 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2363 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2363_checked : acceptsGraphIso
    (source (graph core2363) (root 10) 0 0) DegreeOneSmallSpectrum1771.graph sourceMap2363=true := by decide +kernel
theorem fusedMap2363_checked : acceptsGraphIso
    (fused (graph core2363) (root 10) 0 0) DegreeOneSmallSpectrum1770.graph fusedMap2363=true := by decide +kernel
theorem certified2363 : Certified (graph core2363) (root 10) 0 0 :=
  of_native_maps core2363 DegreeOneSmallSpectrum1771.graph DegreeOneSmallSpectrum1770.graph
    sourceMap2363 fusedMap2363 sourceMap2363_checked fusedMap2363_checked
    DegreeOneSmallComparisons.comparison2363
#print axioms sourceMap2363_checked
#print axioms fusedMap2363_checked
#print axioms certified2363
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
