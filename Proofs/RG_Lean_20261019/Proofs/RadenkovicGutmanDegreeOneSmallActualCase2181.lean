/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2181 : Family 10 := level10.get ⟨666,by decide⟩
def sourceMap2181 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2181 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2181_checked : acceptsGraphIso
    (source (graph core2181) (root 10) 0 0) DegreeOneSmallSpectrum1779.graph sourceMap2181=true := by decide +kernel
theorem fusedMap2181_checked : acceptsGraphIso
    (fused (graph core2181) (root 10) 0 0) DegreeOneSmallSpectrum1283.graph fusedMap2181=true := by decide +kernel
theorem certified2181 : Certified (graph core2181) (root 10) 0 0 :=
  of_native_maps core2181 DegreeOneSmallSpectrum1779.graph DegreeOneSmallSpectrum1283.graph
    sourceMap2181 fusedMap2181 sourceMap2181_checked fusedMap2181_checked
    DegreeOneSmallComparisons.comparison2181
#print axioms sourceMap2181_checked
#print axioms fusedMap2181_checked
#print axioms certified2181
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
