/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2244 : Family 10 := level10.get ⟨800,by decide⟩
def sourceMap2244 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2244 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2244_checked : acceptsGraphIso
    (source (graph core2244) (root 10) 0 0) DegreeOneSmallSpectrum1453.graph sourceMap2244=true := by decide +kernel
theorem fusedMap2244_checked : acceptsGraphIso
    (fused (graph core2244) (root 10) 0 0) DegreeOneSmallSpectrum1452.graph fusedMap2244=true := by decide +kernel
theorem certified2244 : Certified (graph core2244) (root 10) 0 0 :=
  of_native_maps core2244 DegreeOneSmallSpectrum1453.graph DegreeOneSmallSpectrum1452.graph
    sourceMap2244 fusedMap2244 sourceMap2244_checked fusedMap2244_checked
    DegreeOneSmallComparisons.comparison2244
#print axioms sourceMap2244_checked
#print axioms fusedMap2244_checked
#print axioms certified2244
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
