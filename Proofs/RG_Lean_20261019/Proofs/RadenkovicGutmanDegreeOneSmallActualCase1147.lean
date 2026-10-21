/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1147 : Family 8 := level8.get ⟨192,by decide⟩
def sourceMap1147 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,9,10,7,8] (sourceLabel 8 0 0 v)
def fusedMap1147 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1147_checked : acceptsGraphIso
    (source (graph core1147) (root 8) 0 0) DegreeOneSmallSpectrum358.graph sourceMap1147=true := by decide +kernel
theorem fusedMap1147_checked : acceptsGraphIso
    (fused (graph core1147) (root 8) 0 0) DegreeOneSmallSpectrum236.graph fusedMap1147=true := by decide +kernel
theorem certified1147 : Certified (graph core1147) (root 8) 0 0 :=
  of_native_maps core1147 DegreeOneSmallSpectrum358.graph DegreeOneSmallSpectrum236.graph
    sourceMap1147 fusedMap1147 sourceMap1147_checked fusedMap1147_checked
    DegreeOneSmallComparisons.comparison1147
#print axioms sourceMap1147_checked
#print axioms fusedMap1147_checked
#print axioms certified1147
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
