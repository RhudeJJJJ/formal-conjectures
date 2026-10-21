/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1257 : Family 9 := level9.get ⟨36,by decide⟩
def sourceMap1257 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,8,9,10,11,7,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1257 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1257_checked : acceptsGraphIso
    (source (graph core1257) (root 9) 0 0) DegreeOneSmallSpectrum446.graph sourceMap1257=true := by decide +kernel
theorem fusedMap1257_checked : acceptsGraphIso
    (fused (graph core1257) (root 9) 0 0) DegreeOneSmallSpectrum389.graph fusedMap1257=true := by decide +kernel
theorem certified1257 : Certified (graph core1257) (root 9) 0 0 :=
  of_native_maps core1257 DegreeOneSmallSpectrum446.graph DegreeOneSmallSpectrum389.graph
    sourceMap1257 fusedMap1257 sourceMap1257_checked fusedMap1257_checked
    DegreeOneSmallComparisons.comparison1257
#print axioms sourceMap1257_checked
#print axioms fusedMap1257_checked
#print axioms certified1257
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
