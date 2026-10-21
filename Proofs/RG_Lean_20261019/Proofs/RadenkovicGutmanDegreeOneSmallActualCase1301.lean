/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1301 : Family 9 := level9.get ⟨69,by decide⟩
def sourceMap1301 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1301 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1301_checked : acceptsGraphIso
    (source (graph core1301) (root 9) 0 0) DegreeOneSmallSpectrum481.graph sourceMap1301=true := by decide +kernel
theorem fusedMap1301_checked : acceptsGraphIso
    (fused (graph core1301) (root 9) 0 0) DegreeOneSmallSpectrum505.graph fusedMap1301=true := by decide +kernel
theorem certified1301 : Certified (graph core1301) (root 9) 0 0 :=
  of_native_maps core1301 DegreeOneSmallSpectrum481.graph DegreeOneSmallSpectrum505.graph
    sourceMap1301 fusedMap1301 sourceMap1301_checked fusedMap1301_checked
    DegreeOneSmallComparisons.comparison1301
#print axioms sourceMap1301_checked
#print axioms fusedMap1301_checked
#print axioms certified1301
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
