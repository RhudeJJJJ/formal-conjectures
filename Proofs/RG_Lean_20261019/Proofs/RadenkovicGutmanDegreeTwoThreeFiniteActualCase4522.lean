/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4522 : Family 10 := level10.get ⟨361,by decide⟩
def sourceMap4522 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,16,14,15,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4522 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4522_checked : acceptsGraphIso
    (source (graph core4522) (root 10) 2 2) DegreeTwoThreeSpectrum6783.graph sourceMap4522=true := by decide +kernel
theorem fusedMap4522_checked : acceptsGraphIso
    (fused (graph core4522) (root 10) 2 2) DegreeTwoThreeSpectrum5645.graph fusedMap4522=true := by decide +kernel
theorem certified4522 : Certified (graph core4522) (root 10) 2 2 :=
  of_native_maps core4522 DegreeTwoThreeSpectrum6783.graph DegreeTwoThreeSpectrum5645.graph
    sourceMap4522 fusedMap4522 sourceMap4522_checked fusedMap4522_checked
    DegreeTwoThreeFiniteComparisons.comparison4522
#print axioms sourceMap4522_checked
#print axioms fusedMap4522_checked
#print axioms certified4522
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
