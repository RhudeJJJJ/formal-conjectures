/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4042 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap4042 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap4042 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap4042_checked : acceptsGraphIso
    (source (graph core4042) (root 5) 2 2) DegreeOneSmallSpectrum825.graph sourceMap4042=true := by decide +kernel
theorem fusedMap4042_checked : acceptsGraphIso
    (fused (graph core4042) (root 5) 2 2) DegreeOneSmallSpectrum411.graph fusedMap4042=true := by decide +kernel
theorem certified4042 : Certified (graph core4042) (root 5) 2 2 :=
  of_native_maps core4042 DegreeOneSmallSpectrum825.graph DegreeOneSmallSpectrum411.graph
    sourceMap4042 fusedMap4042 sourceMap4042_checked fusedMap4042_checked
    DegreeTwoThreeFiniteComparisons.comparison4042
#print axioms sourceMap4042_checked
#print axioms fusedMap4042_checked
#print axioms certified4042
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
