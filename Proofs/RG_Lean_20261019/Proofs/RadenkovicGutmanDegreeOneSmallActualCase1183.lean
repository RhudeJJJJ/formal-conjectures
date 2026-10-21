/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1183 : Family 8 := level8.get ⟨232,by decide⟩
def sourceMap1183 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1183 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1183_checked : acceptsGraphIso
    (source (graph core1183) (root 8) 0 0) SmallGeFourSpectrum086.graph sourceMap1183=true := by decide +kernel
theorem fusedMap1183_checked : acceptsGraphIso
    (fused (graph core1183) (root 8) 0 0) SmallGeFourSpectrum056.graph fusedMap1183=true := by decide +kernel
theorem certified1183 : Certified (graph core1183) (root 8) 0 0 :=
  of_native_maps core1183 SmallGeFourSpectrum086.graph SmallGeFourSpectrum056.graph
    sourceMap1183 fusedMap1183 sourceMap1183_checked fusedMap1183_checked
    DegreeOneSmallComparisons.comparison1183
#print axioms sourceMap1183_checked
#print axioms fusedMap1183_checked
#print axioms certified1183
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
