/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2182 : Family 10 := level10.get ⟨683,by decide⟩
def sourceMap2182 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2182 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2182_checked : acceptsGraphIso
    (source (graph core2182) (root 10) 0 0) DegreeOneSmallSpectrum1849.graph sourceMap2182=true := by decide +kernel
theorem fusedMap2182_checked : acceptsGraphIso
    (fused (graph core2182) (root 10) 0 0) DegreeOneSmallSpectrum1292.graph fusedMap2182=true := by decide +kernel
theorem certified2182 : Certified (graph core2182) (root 10) 0 0 :=
  of_native_maps core2182 DegreeOneSmallSpectrum1849.graph DegreeOneSmallSpectrum1292.graph
    sourceMap2182 fusedMap2182 sourceMap2182_checked fusedMap2182_checked
    DegreeOneSmallComparisons.comparison2182
#print axioms sourceMap2182_checked
#print axioms fusedMap2182_checked
#print axioms certified2182
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
