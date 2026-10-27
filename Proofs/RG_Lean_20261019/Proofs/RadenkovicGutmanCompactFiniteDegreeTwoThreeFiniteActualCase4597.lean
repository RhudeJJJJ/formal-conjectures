/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4597 : Family 10 := level10.get ⟨594,by decide⟩
def sourceMap4597 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4597 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4597_checked : acceptsGraphIso
    (source (graph core4597) (root 10) 2 2) DegreeTwoThreeSpectrum7241.graph sourceMap4597=true := by decide +kernel
theorem fusedMap4597_checked : acceptsGraphIso
    (fused (graph core4597) (root 10) 2 2) DegreeTwoThreeSpectrum5268.graph fusedMap4597=true := by decide +kernel
theorem certified4597 : Certified (graph core4597) (root 10) 2 2 :=
  of_native_maps core4597 DegreeTwoThreeSpectrum7241.graph DegreeTwoThreeSpectrum5268.graph
    sourceMap4597 fusedMap4597 sourceMap4597_checked fusedMap4597_checked
    DegreeTwoThreeFiniteComparisons.comparison4597
#print axioms sourceMap4597_checked
#print axioms fusedMap4597_checked
#print axioms certified4597
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
