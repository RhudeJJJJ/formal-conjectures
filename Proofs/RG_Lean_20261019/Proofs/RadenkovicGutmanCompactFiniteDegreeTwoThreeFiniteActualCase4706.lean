/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4706 : Family 10 := level10.get ⟨892,by decide⟩
def sourceMap4706 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4706 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4706_checked : acceptsGraphIso
    (source (graph core4706) (root 10) 2 2) DegreeTwoThreeSpectrum7496.graph sourceMap4706=true := by decide +kernel
theorem fusedMap4706_checked : acceptsGraphIso
    (fused (graph core4706) (root 10) 2 2) DegreeTwoThreeSpectrum5750.graph fusedMap4706=true := by decide +kernel
theorem certified4706 : Certified (graph core4706) (root 10) 2 2 :=
  of_native_maps core4706 DegreeTwoThreeSpectrum7496.graph DegreeTwoThreeSpectrum5750.graph
    sourceMap4706 fusedMap4706 sourceMap4706_checked fusedMap4706_checked
    DegreeTwoThreeFiniteComparisons.comparison4706
#print axioms sourceMap4706_checked
#print axioms fusedMap4706_checked
#print axioms certified4706
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
