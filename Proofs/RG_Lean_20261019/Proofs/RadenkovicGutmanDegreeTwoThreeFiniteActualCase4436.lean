/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4436 : Family 10 := level10.get ⟨38,by decide⟩
def sourceMap4436 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4436 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4436_checked : acceptsGraphIso
    (source (graph core4436) (root 10) 2 2) DegreeTwoThreeSpectrum5659.graph sourceMap4436=true := by decide +kernel
theorem fusedMap4436_checked : acceptsGraphIso
    (fused (graph core4436) (root 10) 2 2) DegreeTwoThreeSpectrum5104.graph fusedMap4436=true := by decide +kernel
theorem certified4436 : Certified (graph core4436) (root 10) 2 2 :=
  of_native_maps core4436 DegreeTwoThreeSpectrum5659.graph DegreeTwoThreeSpectrum5104.graph
    sourceMap4436 fusedMap4436 sourceMap4436_checked fusedMap4436_checked
    DegreeTwoThreeFiniteComparisons.comparison4436
#print axioms sourceMap4436_checked
#print axioms fusedMap4436_checked
#print axioms certified4436
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
