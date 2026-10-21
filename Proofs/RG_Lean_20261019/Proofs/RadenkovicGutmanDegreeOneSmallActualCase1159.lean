/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1159 : Family 8 := level8.get ⟨199,by decide⟩
def sourceMap1159 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (sourceLabel 8 0 0 v)
def fusedMap1159 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1159_checked : acceptsGraphIso
    (source (graph core1159) (root 8) 0 0) DegreeOneSmallSpectrum361.graph sourceMap1159=true := by decide +kernel
theorem fusedMap1159_checked : acceptsGraphIso
    (fused (graph core1159) (root 8) 0 0) SmallGeFourSpectrum045.graph fusedMap1159=true := by decide +kernel
theorem certified1159 : Certified (graph core1159) (root 8) 0 0 :=
  of_native_maps core1159 DegreeOneSmallSpectrum361.graph SmallGeFourSpectrum045.graph
    sourceMap1159 fusedMap1159 sourceMap1159_checked fusedMap1159_checked
    DegreeOneSmallComparisons.comparison1159
#print axioms sourceMap1159_checked
#print axioms fusedMap1159_checked
#print axioms certified1159
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
