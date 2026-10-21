/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1063 : Family 8 := level8.get ⟨133,by decide⟩
def sourceMap1063 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,4,5,6,7,8,9,10,2,3] (sourceLabel 8 0 0 v)
def fusedMap1063 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1063_checked : acceptsGraphIso
    (source (graph core1063) (root 8) 0 0) SmallGeFourSpectrum051.graph sourceMap1063=true := by decide +kernel
theorem fusedMap1063_checked : acceptsGraphIso
    (fused (graph core1063) (root 8) 0 0) SmallGeFourSpectrum058.graph fusedMap1063=true := by decide +kernel
theorem certified1063 : Certified (graph core1063) (root 8) 0 0 :=
  of_native_maps core1063 SmallGeFourSpectrum051.graph SmallGeFourSpectrum058.graph
    sourceMap1063 fusedMap1063 sourceMap1063_checked fusedMap1063_checked
    DegreeOneSmallComparisons.comparison1063
#print axioms sourceMap1063_checked
#print axioms fusedMap1063_checked
#print axioms certified1063
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
