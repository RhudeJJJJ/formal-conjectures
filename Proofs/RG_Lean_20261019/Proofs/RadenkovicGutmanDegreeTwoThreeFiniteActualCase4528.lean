/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4528 : Family 10 := level10.get ⟨384,by decide⟩
def sourceMap4528 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4528 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4528_checked : acceptsGraphIso
    (source (graph core4528) (root 10) 2 2) DegreeTwoThreeSpectrum6840.graph sourceMap4528=true := by decide +kernel
theorem fusedMap4528_checked : acceptsGraphIso
    (fused (graph core4528) (root 10) 2 2) DegreeTwoThreeSpectrum5714.graph fusedMap4528=true := by decide +kernel
theorem certified4528 : Certified (graph core4528) (root 10) 2 2 :=
  of_native_maps core4528 DegreeTwoThreeSpectrum6840.graph DegreeTwoThreeSpectrum5714.graph
    sourceMap4528 fusedMap4528 sourceMap4528_checked fusedMap4528_checked
    DegreeTwoThreeFiniteComparisons.comparison4528
#print axioms sourceMap4528_checked
#print axioms fusedMap4528_checked
#print axioms certified4528
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
