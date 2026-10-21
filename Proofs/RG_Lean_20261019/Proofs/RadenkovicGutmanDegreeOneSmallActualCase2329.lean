/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2329 : Family 10 := level10.get ⟨1033,by decide⟩
def sourceMap2329 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2329 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2329_checked : acceptsGraphIso
    (source (graph core2329) (root 10) 0 0) DegreeOneSmallSpectrum1607.graph sourceMap2329=true := by decide +kernel
theorem fusedMap2329_checked : acceptsGraphIso
    (fused (graph core2329) (root 10) 0 0) DegreeOneSmallSpectrum1609.graph fusedMap2329=true := by decide +kernel
theorem certified2329 : Certified (graph core2329) (root 10) 0 0 :=
  of_native_maps core2329 DegreeOneSmallSpectrum1607.graph DegreeOneSmallSpectrum1609.graph
    sourceMap2329 fusedMap2329 sourceMap2329_checked fusedMap2329_checked
    DegreeOneSmallComparisons.comparison2329
#print axioms sourceMap2329_checked
#print axioms fusedMap2329_checked
#print axioms certified2329
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
