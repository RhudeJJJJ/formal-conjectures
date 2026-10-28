/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4857 : Family 10 := level10.get ⟨1271,by decide⟩
def sourceMap4857 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4857 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4857_checked : acceptsGraphIso
    (source (graph core4857) (root 10) 2 2) DegreeTwoThreeSpectrum7357.graph sourceMap4857=true := by decide +kernel
theorem fusedMap4857_checked : acceptsGraphIso
    (fused (graph core4857) (root 10) 2 2) DegreeTwoThreeSpectrum6533.graph fusedMap4857=true := by decide +kernel
theorem certified4857 : Certified (graph core4857) (root 10) 2 2 :=
  of_native_maps core4857 DegreeTwoThreeSpectrum7357.graph DegreeTwoThreeSpectrum6533.graph
    sourceMap4857 fusedMap4857 sourceMap4857_checked fusedMap4857_checked
    DegreeTwoThreeFiniteComparisons.comparison4857
#print axioms sourceMap4857_checked
#print axioms fusedMap4857_checked
#print axioms certified4857
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
