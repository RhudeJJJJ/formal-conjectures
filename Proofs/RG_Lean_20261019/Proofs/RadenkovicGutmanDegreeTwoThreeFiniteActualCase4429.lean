/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4429 : Family 9 := level9.get ⟨691,by decide⟩
def sourceMap4429 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4429 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4429_checked : acceptsGraphIso
    (source (graph core4429) (root 9) 2 2) DegreeTwoThreeSpectrum4956.graph sourceMap4429=true := by decide +kernel
theorem fusedMap4429_checked : acceptsGraphIso
    (fused (graph core4429) (root 9) 2 2) DegreeTwoThreeSpectrum4667.graph fusedMap4429=true := by decide +kernel
theorem certified4429 : Certified (graph core4429) (root 9) 2 2 :=
  of_native_maps core4429 DegreeTwoThreeSpectrum4956.graph DegreeTwoThreeSpectrum4667.graph
    sourceMap4429 fusedMap4429 sourceMap4429_checked fusedMap4429_checked
    DegreeTwoThreeFiniteComparisons.comparison4429
#print axioms sourceMap4429_checked
#print axioms fusedMap4429_checked
#print axioms certified4429
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
