/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4202 : Family 9 := level9.get ⟨54,by decide⟩
def sourceMap4202 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4202 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4202_checked : acceptsGraphIso
    (source (graph core4202) (root 9) 2 2) DegreeTwoThreeSpectrum4327.graph sourceMap4202=true := by decide +kernel
theorem fusedMap4202_checked : acceptsGraphIso
    (fused (graph core4202) (root 9) 2 2) DegreeTwoThreeSpectrum3940.graph fusedMap4202=true := by decide +kernel
theorem certified4202 : Certified (graph core4202) (root 9) 2 2 :=
  of_native_maps core4202 DegreeTwoThreeSpectrum4327.graph DegreeTwoThreeSpectrum3940.graph
    sourceMap4202 fusedMap4202 sourceMap4202_checked fusedMap4202_checked
    DegreeTwoThreeFiniteComparisons.comparison4202
#print axioms sourceMap4202_checked
#print axioms fusedMap4202_checked
#print axioms certified4202
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
