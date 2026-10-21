/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2196 : Family 10 := level10.get ⟨703,by decide⟩
def sourceMap2196 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2196 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2196_checked : acceptsGraphIso
    (source (graph core2196) (root 10) 0 0) DegreeOneSmallSpectrum1822.graph sourceMap2196=true := by decide +kernel
theorem fusedMap2196_checked : acceptsGraphIso
    (fused (graph core2196) (root 10) 0 0) DegreeOneSmallSpectrum1318.graph fusedMap2196=true := by decide +kernel
theorem certified2196 : Certified (graph core2196) (root 10) 0 0 :=
  of_native_maps core2196 DegreeOneSmallSpectrum1822.graph DegreeOneSmallSpectrum1318.graph
    sourceMap2196 fusedMap2196 sourceMap2196_checked fusedMap2196_checked
    DegreeOneSmallComparisons.comparison2196
#print axioms sourceMap2196_checked
#print axioms fusedMap2196_checked
#print axioms certified2196
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
