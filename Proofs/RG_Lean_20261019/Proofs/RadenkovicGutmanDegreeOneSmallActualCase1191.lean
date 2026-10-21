/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1191 : Family 8 := level8.get ⟨264,by decide⟩
def sourceMap1191 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (sourceLabel 8 0 0 v)
def fusedMap1191 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1191_checked : acceptsGraphIso
    (source (graph core1191) (root 8) 0 0) SmallGeFourSpectrum070.graph sourceMap1191=true := by decide +kernel
theorem fusedMap1191_checked : acceptsGraphIso
    (fused (graph core1191) (root 8) 0 0) SmallGeFourSpectrum071.graph fusedMap1191=true := by decide +kernel
theorem certified1191 : Certified (graph core1191) (root 8) 0 0 :=
  of_native_maps core1191 SmallGeFourSpectrum070.graph SmallGeFourSpectrum071.graph
    sourceMap1191 fusedMap1191 sourceMap1191_checked fusedMap1191_checked
    DegreeOneSmallComparisons.comparison1191
#print axioms sourceMap1191_checked
#print axioms fusedMap1191_checked
#print axioms certified1191
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
