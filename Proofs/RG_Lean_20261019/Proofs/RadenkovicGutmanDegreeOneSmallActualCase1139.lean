/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1139 : Family 8 := level8.get ⟨189,by decide⟩
def sourceMap1139 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap1139 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1139_checked : acceptsGraphIso
    (source (graph core1139) (root 8) 0 0) SmallGeFourSpectrum077.graph sourceMap1139=true := by decide +kernel
theorem fusedMap1139_checked : acceptsGraphIso
    (fused (graph core1139) (root 8) 0 0) SmallGeFourSpectrum041.graph fusedMap1139=true := by decide +kernel
theorem certified1139 : Certified (graph core1139) (root 8) 0 0 :=
  of_native_maps core1139 SmallGeFourSpectrum077.graph SmallGeFourSpectrum041.graph
    sourceMap1139 fusedMap1139 sourceMap1139_checked fusedMap1139_checked
    DegreeOneSmallComparisons.comparison1139
#print axioms sourceMap1139_checked
#print axioms fusedMap1139_checked
#print axioms certified1139
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
