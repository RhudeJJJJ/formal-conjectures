/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2275 : Family 10 := level10.get ⟨867,by decide⟩
def sourceMap2275 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2275 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2275_checked : acceptsGraphIso
    (source (graph core2275) (root 10) 0 0) DegreeOneSmallSpectrum1792.graph sourceMap2275=true := by decide +kernel
theorem fusedMap2275_checked : acceptsGraphIso
    (fused (graph core2275) (root 10) 0 0) DegreeOneSmallSpectrum1487.graph fusedMap2275=true := by decide +kernel
theorem certified2275 : Certified (graph core2275) (root 10) 0 0 :=
  of_native_maps core2275 DegreeOneSmallSpectrum1792.graph DegreeOneSmallSpectrum1487.graph
    sourceMap2275 fusedMap2275 sourceMap2275_checked fusedMap2275_checked
    DegreeOneSmallComparisons.comparison2275
#print axioms sourceMap2275_checked
#print axioms fusedMap2275_checked
#print axioms certified2275
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
