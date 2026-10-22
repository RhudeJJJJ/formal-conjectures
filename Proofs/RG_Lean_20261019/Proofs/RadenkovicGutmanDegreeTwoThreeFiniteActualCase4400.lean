/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4400 : Family 9 := level9.get ⟨596,by decide⟩
def sourceMap4400 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4400 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4400_checked : acceptsGraphIso
    (source (graph core4400) (root 9) 2 2) DegreeTwoThreeSpectrum4927.graph sourceMap4400=true := by decide +kernel
theorem fusedMap4400_checked : acceptsGraphIso
    (fused (graph core4400) (root 9) 2 2) DegreeTwoThreeSpectrum4275.graph fusedMap4400=true := by decide +kernel
theorem certified4400 : Certified (graph core4400) (root 9) 2 2 :=
  of_native_maps core4400 DegreeTwoThreeSpectrum4927.graph DegreeTwoThreeSpectrum4275.graph
    sourceMap4400 fusedMap4400 sourceMap4400_checked fusedMap4400_checked
    DegreeTwoThreeFiniteComparisons.comparison4400
#print axioms sourceMap4400_checked
#print axioms fusedMap4400_checked
#print axioms certified4400
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
