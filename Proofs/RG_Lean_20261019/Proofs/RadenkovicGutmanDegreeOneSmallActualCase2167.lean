/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2167 : Family 10 := level10.get ⟨636,by decide⟩
def sourceMap2167 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2167 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2167_checked : acceptsGraphIso
    (source (graph core2167) (root 10) 0 0) DegreeOneSmallSpectrum1760.graph sourceMap2167=true := by decide +kernel
theorem fusedMap2167_checked : acceptsGraphIso
    (fused (graph core2167) (root 10) 0 0) DegreeOneSmallSpectrum1223.graph fusedMap2167=true := by decide +kernel
theorem certified2167 : Certified (graph core2167) (root 10) 0 0 :=
  of_native_maps core2167 DegreeOneSmallSpectrum1760.graph DegreeOneSmallSpectrum1223.graph
    sourceMap2167 fusedMap2167 sourceMap2167_checked fusedMap2167_checked
    DegreeOneSmallComparisons.comparison2167
#print axioms sourceMap2167_checked
#print axioms fusedMap2167_checked
#print axioms certified2167
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
