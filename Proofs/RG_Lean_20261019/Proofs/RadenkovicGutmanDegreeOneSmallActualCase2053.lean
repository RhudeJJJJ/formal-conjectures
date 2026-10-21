/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2053 : Family 10 := level10.get ⟨420,by decide⟩
def sourceMap2053 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2053 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2053_checked : acceptsGraphIso
    (source (graph core2053) (root 10) 0 0) DegreeOneSmallSpectrum1117.graph sourceMap2053=true := by decide +kernel
theorem fusedMap2053_checked : acceptsGraphIso
    (fused (graph core2053) (root 10) 0 0) DegreeOneSmallSpectrum1496.graph fusedMap2053=true := by decide +kernel
theorem certified2053 : Certified (graph core2053) (root 10) 0 0 :=
  of_native_maps core2053 DegreeOneSmallSpectrum1117.graph DegreeOneSmallSpectrum1496.graph
    sourceMap2053 fusedMap2053 sourceMap2053_checked fusedMap2053_checked
    DegreeOneSmallComparisons.comparison2053
#print axioms sourceMap2053_checked
#print axioms fusedMap2053_checked
#print axioms certified2053
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
