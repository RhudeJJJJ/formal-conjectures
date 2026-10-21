/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1174 : Family 8 := level8.get ⟨210,by decide⟩
def sourceMap1174 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1174 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1174_checked : acceptsGraphIso
    (source (graph core1174) (root 8) 1 1) DegreeOneSmallSpectrum1740.graph sourceMap1174=true := by decide +kernel
theorem fusedMap1174_checked : acceptsGraphIso
    (fused (graph core1174) (root 8) 1 1) DegreeOneSmallSpectrum1090.graph fusedMap1174=true := by decide +kernel
theorem certified1174 : Certified (graph core1174) (root 8) 1 1 :=
  of_native_maps core1174 DegreeOneSmallSpectrum1740.graph DegreeOneSmallSpectrum1090.graph
    sourceMap1174 fusedMap1174 sourceMap1174_checked fusedMap1174_checked
    DegreeOneSmallComparisons.comparison1174
#print axioms sourceMap1174_checked
#print axioms fusedMap1174_checked
#print axioms certified1174
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
