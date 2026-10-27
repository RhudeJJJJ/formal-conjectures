/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4545 : Family 10 := level10.get ⟨437,by decide⟩
def sourceMap4545 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4545 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4545_checked : acceptsGraphIso
    (source (graph core4545) (root 10) 2 2) DegreeTwoThreeSpectrum6850.graph sourceMap4545=true := by decide +kernel
theorem fusedMap4545_checked : acceptsGraphIso
    (fused (graph core4545) (root 10) 2 2) DegreeTwoThreeSpectrum5849.graph fusedMap4545=true := by decide +kernel
theorem certified4545 : Certified (graph core4545) (root 10) 2 2 :=
  of_native_maps core4545 DegreeTwoThreeSpectrum6850.graph DegreeTwoThreeSpectrum5849.graph
    sourceMap4545 fusedMap4545 sourceMap4545_checked fusedMap4545_checked
    DegreeTwoThreeFiniteComparisons.comparison4545
#print axioms sourceMap4545_checked
#print axioms fusedMap4545_checked
#print axioms certified4545
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
