/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2145 : Family 10 := level10.get ⟨595,by decide⟩
def sourceMap2145 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2145 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2145_checked : acceptsGraphIso
    (source (graph core2145) (root 10) 0 0) DegreeOneSmallSpectrum1816.graph sourceMap2145=true := by decide +kernel
theorem fusedMap2145_checked : acceptsGraphIso
    (fused (graph core2145) (root 10) 0 0) DegreeOneSmallSpectrum1143.graph fusedMap2145=true := by decide +kernel
theorem certified2145 : Certified (graph core2145) (root 10) 0 0 :=
  of_native_maps core2145 DegreeOneSmallSpectrum1816.graph DegreeOneSmallSpectrum1143.graph
    sourceMap2145 fusedMap2145 sourceMap2145_checked fusedMap2145_checked
    DegreeOneSmallComparisons.comparison2145
#print axioms sourceMap2145_checked
#print axioms fusedMap2145_checked
#print axioms certified2145
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
