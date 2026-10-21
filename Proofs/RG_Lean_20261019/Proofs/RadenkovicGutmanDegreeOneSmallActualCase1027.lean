/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1027 : Family 8 := level8.get ⟨112,by decide⟩
def sourceMap1027 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap1027 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1027_checked : acceptsGraphIso
    (source (graph core1027) (root 8) 0 0) DegreeOneSmallSpectrum283.graph sourceMap1027=true := by decide +kernel
theorem fusedMap1027_checked : acceptsGraphIso
    (fused (graph core1027) (root 8) 0 0) SmallGeFourSpectrum049.graph fusedMap1027=true := by decide +kernel
theorem certified1027 : Certified (graph core1027) (root 8) 0 0 :=
  of_native_maps core1027 DegreeOneSmallSpectrum283.graph SmallGeFourSpectrum049.graph
    sourceMap1027 fusedMap1027 sourceMap1027_checked fusedMap1027_checked
    DegreeOneSmallComparisons.comparison1027
#print axioms sourceMap1027_checked
#print axioms fusedMap1027_checked
#print axioms certified1027
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
