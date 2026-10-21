/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1987 : Family 10 := level10.get ⟨312,by decide⟩
def sourceMap1987 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1987 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1987_checked : acceptsGraphIso
    (source (graph core1987) (root 10) 0 0) DegreeOneSmallSpectrum1168.graph sourceMap1987=true := by decide +kernel
theorem fusedMap1987_checked : acceptsGraphIso
    (fused (graph core1987) (root 10) 0 0) DegreeOneSmallSpectrum1379.graph fusedMap1987=true := by decide +kernel
theorem certified1987 : Certified (graph core1987) (root 10) 0 0 :=
  of_native_maps core1987 DegreeOneSmallSpectrum1168.graph DegreeOneSmallSpectrum1379.graph
    sourceMap1987 fusedMap1987 sourceMap1987_checked fusedMap1987_checked
    DegreeOneSmallComparisons.comparison1987
#print axioms sourceMap1987_checked
#print axioms fusedMap1987_checked
#print axioms certified1987
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
