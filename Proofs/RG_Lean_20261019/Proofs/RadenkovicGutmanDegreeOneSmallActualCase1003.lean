/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1003 : Family 8 := level8.get ⟨101,by decide⟩
def sourceMap1003 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap1003 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap1003_checked : acceptsGraphIso
    (source (graph core1003) (root 8) 0 0) DegreeOneSmallSpectrum254.graph sourceMap1003=true := by decide +kernel
theorem fusedMap1003_checked : acceptsGraphIso
    (fused (graph core1003) (root 8) 0 0) DegreeOneSmallSpectrum258.graph fusedMap1003=true := by decide +kernel
theorem certified1003 : Certified (graph core1003) (root 8) 0 0 :=
  of_native_maps core1003 DegreeOneSmallSpectrum254.graph DegreeOneSmallSpectrum258.graph
    sourceMap1003 fusedMap1003 sourceMap1003_checked fusedMap1003_checked
    DegreeOneSmallComparisons.comparison1003
#print axioms sourceMap1003_checked
#print axioms fusedMap1003_checked
#print axioms certified1003
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
