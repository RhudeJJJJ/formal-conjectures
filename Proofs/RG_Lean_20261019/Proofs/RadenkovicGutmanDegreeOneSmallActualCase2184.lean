/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2184 : Family 10 := level10.get ⟨685,by decide⟩
def sourceMap2184 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2184 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2184_checked : acceptsGraphIso
    (source (graph core2184) (root 10) 0 0) DegreeOneSmallSpectrum1818.graph sourceMap2184=true := by decide +kernel
theorem fusedMap2184_checked : acceptsGraphIso
    (fused (graph core2184) (root 10) 0 0) DegreeOneSmallSpectrum1295.graph fusedMap2184=true := by decide +kernel
theorem certified2184 : Certified (graph core2184) (root 10) 0 0 :=
  of_native_maps core2184 DegreeOneSmallSpectrum1818.graph DegreeOneSmallSpectrum1295.graph
    sourceMap2184 fusedMap2184 sourceMap2184_checked fusedMap2184_checked
    DegreeOneSmallComparisons.comparison2184
#print axioms sourceMap2184_checked
#print axioms fusedMap2184_checked
#print axioms certified2184
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
