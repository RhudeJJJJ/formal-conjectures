/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1099 : Family 8 := level8.get ⟨150,by decide⟩
def sourceMap1099 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (sourceLabel 8 0 0 v)
def fusedMap1099 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap1099_checked : acceptsGraphIso
    (source (graph core1099) (root 8) 0 0) DegreeOneSmallSpectrum269.graph sourceMap1099=true := by decide +kernel
theorem fusedMap1099_checked : acceptsGraphIso
    (fused (graph core1099) (root 8) 0 0) DegreeOneSmallSpectrum342.graph fusedMap1099=true := by decide +kernel
theorem certified1099 : Certified (graph core1099) (root 8) 0 0 :=
  of_native_maps core1099 DegreeOneSmallSpectrum269.graph DegreeOneSmallSpectrum342.graph
    sourceMap1099 fusedMap1099 sourceMap1099_checked fusedMap1099_checked
    DegreeOneSmallComparisons.comparison1099
#print axioms sourceMap1099_checked
#print axioms fusedMap1099_checked
#print axioms certified1099
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
